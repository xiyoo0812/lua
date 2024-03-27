/*
** $Id: lgc.c $
** Garbage Collector
** See Copyright Notice in lua.h
*/

#define lgc_c
#define LUA_CORE

#include "lprefix.h"

#include <string.h>


#include "lua.h"

#include "ldebug.h"
#include "ldo.h"
#include "lfunc.h"
#include "lgc.h"
#include "llex.h"
#include "lmem.h"
#include "lobject.h"
#include "lstate.h"
#include "lstring.h"
#include "ltable.h"
#include "ltm.h"


/*
** Number of fixed (luaC_fix) objects in a Lua state: metafield names,
** plus reserved words, plus "_ENV", plus the memory-error message.
*/
#define NFIXED		(TM_N + NUM_RESERVED + 2)


/*
** Maximum number of elements to sweep in each single step.
** (Large enough to dissipate fixed overheads but small enough
** to allow small steps for the collector.)
*/
#define GCSWEEPMAX	20


/* mask with all color bits */
/* maskcolors 等于 gary（灰色） */
#define maskcolors	(bitmask(BLACKBIT) | WHITEBITS)

/* mask with all GC bits */
/* 默认mark值，age为111（AGEBITS），相当于没有设置age*/
#define maskgcbits      (maskcolors | AGEBITS)


/* macro to erase all color bits then set only the current white bit */
/* 标记为白色，先清除age和black */
#define makewhite(g,x)	\
  (x->marked = cast_byte((x->marked & ~maskcolors) | luaC_white(g)))

/* make an object gray (neither white nor black) */
/* 设置为灰色 */
#define set2gray(x)	resetbits(x->marked, maskcolors)


/* make an object black (coming from any color) */
/* 设置为黑色 */
#define set2black(x)  \
  (x->marked = cast_byte((x->marked & ~WHITEBITS) | bitmask(BLACKBIT)))


/* value是否白色，可回收+white */
#define valiswhite(x)   (iscollectable(x) && iswhite(gcvalue(x)))

/* key是否白色，可回收+white */
#define keyiswhite(n)   (keyiscollectable(n) && iswhite(gckey(n)))


/*
** Protected access to objects in values
*/
/* 获取一个可回收对象 */
#define gcvalueN(o)     (iscollectable(o) ? gcvalue(o) : NULL)


/*
** Access to collectable objects in array part of tables
*/
#define gcvalarr(t,i)  \
	((*getArrTag(t,i) & BIT_ISCOLLECTABLE) ? getArrVal(t,i)->gc : NULL)


/* markvalue：标记一个值 */
#define markvalue(g,o) { checkliveness(g->mainthread,o); \
  if (valiswhite(o)) reallymarkobject(g,gcvalue(o)); }

/* markkey：标记一个key值 */
#define markkey(g, n)	{ if keyiswhite(n) reallymarkobject(g,gckey(n)); }

/* markobject：标记一个object */
#define markobject(g,t)	{ if (iswhite(t)) reallymarkobject(g, obj2gco(t)); }

/*
** mark an object that can be NULL (either because it is really optional,
** or it was stripped as debug info, or inside an uncompleted structure)
*/
/* markobjectN：标记一个object,可以为NULL */
#define markobjectN(g,t)	{ if (t) markobject(g,t); }


static void reallymarkobject (global_State *g, GCObject *o);
static l_obj atomic (lua_State *L);
static void entersweep (lua_State *L);


/*
** {======================================================
** Generic functions
** =======================================================
*/


/*
** one after last element in a hash array
*/
// 获取一个hash数组的array的最后一个值，通过数组的长度转换
#define gnodelast(h)	gnode(h, cast_sizet(sizenode(h)))


// 根据类型获取一gc对象管理的gclist
static GCObject **getgclist (GCObject *o) {
  switch (o->tt) {
    case LUA_VTABLE: return &gco2t(o)->gclist;
    case LUA_VLCL: return &gco2lcl(o)->gclist;
    case LUA_VCCL: return &gco2ccl(o)->gclist;
    case LUA_VTHREAD: return &gco2th(o)->gclist;
    case LUA_VPROTO: return &gco2p(o)->gclist;
    case LUA_VUSERDATA: {
      Udata *u = gco2u(o);
      lua_assert(u->nuvalue > 0);
      return &u->gclist;
    }
    default: lua_assert(0); return 0;
  }
}


/*
** Link a collectable object 'o' with a known type into the list 'p'.
** (Must be a macro to access the 'gclist' field in different types.)
*/
/* 链接一个可被收集的对象到链表p，o必须能访问gclist */
#define linkgclist(o,p)	linkgclist_(obj2gco(o), &(o)->gclist, &(p))

/*
将一个对象（不是灰色）链接到链表list，并置为灰色
1）o->gclist = p; p = o;
2）置为灰色
*/
static void linkgclist_ (GCObject *o, GCObject **pnext, GCObject **list) {
  lua_assert(!isgray(o));  /* cannot be in a gray list */
  *pnext = *list;
  *list = o;
  set2gray(o);  /* now it is */
}


/*
** Link a generic collectable object 'o' into the list 'p'.
*/
/* 
链接一个可被收集的对象到链表p，o不能直接访问gclist
1）调用getgclist函数，获取gclist
2）调用linkgclist_
*/
#define linkobjgclist(o,p) linkgclist_(obj2gco(o), getgclist(o), &(p))



/*
** Clear keys for empty entries in tables. If entry is empty, mark its
** entry as dead. This allows the collection of the key, but keeps its
** entry in the table: its removal could break a chain and could break
** a table traversal.  Other places never manipulate dead keys, because
** its associated empty value is enough to signal that the entry is
** logically empty.
*/
/*
清除一个key，防止中断表遍历
1）判断key可以被回收
2）设置为deadkey
*/
static void clearkey (Node *n) {
  lua_assert(isempty(gval(n)));
  if (keyiscollectable(n))
    setdeadkey(n);  /* unused key; remove it */
}


/*
** tells whether a key or value can be cleared from a weak
** table. Non-collectable objects are never removed from weak
** tables. Strings behave as 'values', so are never removed too. for
** other objects: if really collected, cannot keep them; for objects
** being finalized, keep them in keys, but not in values
*/
/*
判断弱表中一个key或者value是否可以被清除
字符串是存在字符串表，永远不是弱引用
*/
static int iscleared (global_State *g, const GCObject *o) {
  if (o == NULL) return 0;  /* non-collectable value */
  else if (novariant(o->tt) == LUA_TSTRING) {
    markobject(g, o);  /* strings are 'values', so are never weak */
    return 0;
  }
  else return iswhite(o);
}


/*
** Barrier that moves collector forward, that is, marks the white object
** 'v' being pointed by the black object 'o'.  In the generational
** mode, 'v' must also become old, if 'o' is old; however, it cannot
** be changed directly to OLD, because it may still point to non-old
** objects. So, it is marked as OLD0. In the next cycle it will become
** OLD1, and in the next it will finally become OLD (regular old). By
** then, any object it points to will also be old.  If called in the
** incremental sweep phase, it clears the black object to white (sweep
** it) to avoid other barrier calls for this same object. (That cannot
** be done is generational mode, as its sweep does not distinguish
** whites from deads.)
*/
/*
将收集器向前移动的屏障
在代际模式中，如果o变老了，v也必须变老，如果o变老了,但是，它不能直接更改为旧对象，因为它可能仍然指向非旧对象。
因此，它被标记为OLD0。在下一个循环中，它将变老1，在下一个循环中，它将最终变老（常规旧）。到那时，它指向的任何对象都将是旧的。
如果在增量模式扫描阶段调用，它会将黑色对象清除为白色（扫描），以避免对同一对象调用其他屏障
1）在稳定阶段，重新标记白色对象，并将其age设置为old0
2）在增量模式扫描阶段，直接将黑色变成白色，重新扫描
*/
void luaC_barrier_ (lua_State *L, GCObject *o, GCObject *v) {
  global_State *g = G(L);
  lua_assert(isblack(o) && iswhite(v) && !isdead(g, v) && !isdead(g, o));
  if (keepinvariant(g)) {  /* must keep invariant? */
    reallymarkobject(g, v);  /* restore invariant */
    if (isold(o)) {
      lua_assert(!isold(v));  /* white object could not be old */
      setage(v, G_OLD0);  /* restore generational invariant */
    }
  }
  else {  /* sweep phase */
    lua_assert(issweepphase(g));
    if (g->gckind != KGC_GENMINOR)  /* incremental mode? */
      makewhite(g, o);  /* mark 'o' as white to avoid other barriers */
  }
}


/*
** barrier that moves collector backward, that is, mark the black object
** pointing to a white object as gray again.
*/
/*
将收集器向后移动的屏障，即将指向白色对象的黑色对象再次标记为灰色。
1）如果对象的age是touch2，标识已经在gray中，则将该对象标记为gray
2）否则加到grayagain
3）如果是分代模式，并且已经old了，则修改为当touch1
*/
void luaC_barrierback_ (lua_State *L, GCObject *o) {
  global_State *g = G(L);
  lua_assert(isblack(o) && !isdead(g, o));
  lua_assert((g->gckind != KGC_GENMINOR)
          || (isold(o) && getage(o) != G_TOUCHED1));
  if (getage(o) == G_TOUCHED2)  /* already in gray list? */
    set2gray(o);  /* make it gray to become touched1 */
  else  /* link it in 'grayagain' and paint it gray */
    linkobjgclist(o, g->grayagain);
  if (isold(o))  /* generational mode? */
    setage(o, G_TOUCHED1);  /* touched in current cycle */
}


/*
标记某些对象，并设置为old，用于存储一些永不释放的对象
1）必须在刚创建时调用
2）设置gray并设置为OLD
3）从allgc中移除
4）加入到fixedgc
*/
void luaC_fix (lua_State *L, GCObject *o) {
  global_State *g = G(L);
  lua_assert(g->allgc == o);  /* object must be 1st in 'allgc' list! */
  set2gray(o);  /* they will be gray forever */
  setage(o, G_OLD);  /* and old forever */
  g->allgc = o->next;  /* remove object from 'allgc' list */
  o->next = g->fixedgc;  /* link it to 'fixedgc' list */
  g->fixedgc = o;
}


/*
** create a new collectable object (with given type, size, and offset)
** and link it to 'allgc' list.
*/
/*
新建一个对象
1）分配一个对象
2）标记为白色，并设置类型
3）添加到allgc链表的head
*/
GCObject *luaC_newobjdt (lua_State *L, int tt, size_t sz, size_t offset) {
  global_State *g = G(L);
  char *p = cast_charp(luaM_newobject(L, novariant(tt), sz));
  GCObject *o = cast(GCObject *, p + offset);
  g->GCdebt--;
  o->marked = luaC_white(g);
  o->tt = tt;
  o->next = g->allgc;
  g->allgc = o;
  return o;
}


/*
** create a new collectable object with no offset.
*/
GCObject *luaC_newobj (lua_State *L, int tt, size_t sz) {
  return luaC_newobjdt(L, tt, sz, 0);
}

/* }====================================================== */



/*
** {======================================================
** Mark functions
** =======================================================
*/


/*
** Mark an object.  Userdata with no user values, strings, and closed
** upvalues are visited and turned black here.  Open upvalues are
** already indirectly linked through their respective threads in the
** 'twups' list, so they don't go to the gray list; nevertheless, they
** are kept gray to avoid barriers, as their values will be revisited
** by the thread or by 'remarkupvals'.  Other objects are added to the
** gray list to be visited (and turned black) later.  Both userdata and
** upvalues can call this function recursively, but this recursion goes
** for at most two levels: An upvalue cannot refer to another upvalue
** (only closures can), and a userdata's metatable must be a table.
*/
/* 标记一个对象 */
static void reallymarkobject (global_State *g, GCObject *o) {
  g->marked++;
  switch (o->tt) {
    case LUA_VSHRSTR:
    case LUA_VLNGSTR: {
      set2black(o);  /* nothing to visit */
      break;
    }
    case LUA_VUPVAL: {
      UpVal *uv = gco2upv(o);
      if (upisopen(uv))
        set2gray(uv);  /* open upvalues are kept gray */
      else
        set2black(uv);  /* closed upvalues are visited here */
      markvalue(g, uv->v.p);  /* mark its content */
      break;
    }
    case LUA_VUSERDATA: {
      Udata *u = gco2u(o);
      if (u->nuvalue == 0) {  /* no user values? */
        markobjectN(g, u->metatable);  /* mark its metatable */
        set2black(u);  /* nothing else to mark */
        break;
      }
      /* else... */
    }  /* FALLTHROUGH */
    case LUA_VLCL: case LUA_VCCL: case LUA_VTABLE:
    case LUA_VTHREAD: case LUA_VPROTO: {
      linkobjgclist(o, g->gray);  /* to be visited later */
      break;
    }
    default: lua_assert(0); break;
  }
}


/*
** mark metamethods for basic types
*/
/* 标记基本类型的元表 */
static void markmt (global_State *g) {
  int i;
  for (i=0; i < LUA_NUMTYPES; i++)
    markobjectN(g, g->mt[i]);
}


/* 标记即将被终止的所有对象 */
/*
** mark all objects in list of being-finalized
*/
static l_obj markbeingfnz (global_State *g) {
  GCObject *o;
  l_obj count = 0;
  for (o = g->tobefnz; o != NULL; o = o->next) {
    count++;
    markobject(g, o);
  }
  return count;
}


/*
重新标记upvalues
1）遍历所有的攸twups中的thread
2）如果thread没有被标记或者没有upvalues
3）将thread从twups删除
4）遍历thread的所有upvalue
5）如果upvalue被标记了，则标记upvalue的值
*/
/*
** For each non-marked thread, simulates a barrier between each open
** upvalue and its value. (If the thread is collected, the value will be
** assigned to the upvalue, but then it can be too late for the barrier
** to act. The "barrier" does not need to check colors: A non-marked
** thread must be young; upvalues cannot be older than their threads; so
** any visited upvalue must be young too.) Also removes the thread from
** the list, as it was already visited. Removes also threads with no
** upvalues, as they have nothing to be checked. (If the thread gets an
** upvalue later, it will be linked in the list again.)
*/
static l_obj remarkupvals (global_State *g) {
  l_obj work = 0;
  lua_State *thread;
  lua_State **p = &g->twups;
  while ((thread = *p) != NULL) {
    if (!iswhite(thread) && thread->openupval != NULL)
      p = &thread->twups;  /* keep marked thread with upvalues in the list */
    else {  /* thread is not marked or without upvalues */
      UpVal *uv;
      lua_assert(!isold(thread) || thread->openupval == NULL);
      *p = thread->twups;  /* remove thread from the list */
      thread->twups = thread;  /* mark that it is out of list */
      for (uv = thread->openupval; uv != NULL; uv = uv->u.open.next) {
        lua_assert(getage(uv) <= getage(thread));
        if (!iswhite(uv)) {  /* upvalue already visited? */
          lua_assert(upisopen(uv) && isgray(uv));
          markvalue(g, uv->v.p);  /* mark its value */
        }
      }
    }
    work++;
  }
  return work;
}


// 清空灰色列表graylist
static void cleargraylists (global_State *g) {
  g->gray = g->grayagain = NULL;
  g->weak = g->allweak = g->ephemeron = NULL;
}


/*
** mark root set and reset all gray lists, to start a new collection.
** 'marked' is initialized with the number of fixed objects in the state,
** to count the total number of live objects during a cycle. (That is
** the metafield names, plus the reserved words, plus "_ENV" plus the
** memory-error message.)
*/
/*
重启一次收集
1）先把graylist清空
2）开始从跟节点标记对象
3）标记注册表的对象
4）标记基础类型的元表
5）标记即将终止的对象
*/
static void restartcollection (global_State *g) {
  cleargraylists(g);
  g->marked = NFIXED;
  markobject(g, g->mainthread);
  markvalue(g, &g->l_registry);
  markmt(g);
  markbeingfnz(g);  /* mark any finalizing object left from previous cycle */
}

/* }====================================================== */


/*
** {======================================================
** Traverse functions
** =======================================================
*/


/*
** Check whether object 'o' should be kept in the 'grayagain' list for
** post-processing by 'correctgraylist'. (It could put all old objects
** in the list and leave all the work to 'correctgraylist', but it is
** more efficient to avoid adding elements that will be removed.) Only
** TOUCHED1 objects need to be in the list. TOUCHED2 doesn't need to go
** back to a gray list, but then it must become OLD. (That is what
** 'correctgraylist' does when it finds a TOUCHED2 object.)
*/
/*
分代收集处理对象age
1）如果是本次循环扫描到了，则重新加入到garylist
2）如果是上次循环扫描到了，则是标记age为OLD
*/
static void genlink (global_State *g, GCObject *o) {
  lua_assert(isblack(o));
  if (getage(o) == G_TOUCHED1) {  /* touched in this cycle? */
    linkobjgclist(o, g->grayagain);  /* link it back in 'grayagain' */
  }  /* everything else do not need to be linked back */
  else if (getage(o) == G_TOUCHED2)
    setage(o, G_OLD);  /* advance age */
}


/*
** Traverse a table with weak values and link it to proper list. During
** propagate phase, keep it in 'grayagain' list, to be revisited in the
** atomic phase. In the atomic phase, if table has any white value,
** put it in 'weak' list, to be cleared.
*/
/*
遍历一个弱value的表并将其链接到适当的列表。
1）获取表的最后一个hash元素limit，以及检查是否是纯hash表，用hasclears标记
2）遍历表的hash部分，如果值为空，则设置key为deadkey
3）如果不为空，这先标记key，然后如果是纯hash表，并且value是白色，则设置hasclears标记位
4）如果在atomic阶段，并且hasclears标记存在，则将此表放入weak链表，准备清除
5）在其他阶段，则放入grayagain，以便在atomic阶段再次扫描
*/
static void traverseweakvalue (global_State *g, Table *h) {
  Node *n, *limit = gnodelast(h);
  /* if there is array part, assume it may have white values (it is not
     worth traversing it now just to check) */
  int hasclears = (h->alimit > 0);
  for (n = gnode(h, 0); n < limit; n++) {  /* traverse hash part */
    if (isempty(gval(n)))  /* entry is empty? */
      clearkey(n);  /* clear its key */
    else {
      lua_assert(!keyisnil(n));
      markkey(g, n);
      if (!hasclears && iscleared(g, gcvalueN(gval(n))))  /* a white value? */
        hasclears = 1;  /* table will have to be cleared */
    }
  }
  if (g->gcstate == GCSatomic && hasclears)
    linkgclist(h, g->weak);  /* has to be cleared later */
  else
    linkgclist(h, g->grayagain);  /* must retraverse it in atomic phase */
}


/*
** Traverse the array part of a table.
*/
static int traversearray (global_State *g, Table *h) {
  unsigned asize = luaH_realasize(h);
  int marked = 0;  /* true if some object is marked in this traversal */
  unsigned i;
  for (i = 0; i < asize; i++) {
    GCObject *o = gcvalarr(h, i);
    if (o != NULL && iswhite(o)) {
      marked = 1;
      reallymarkobject(g, o);
    }
  }
  return marked;
}


/*
** Traverse an ephemeron table and link it to proper list. Returns true
** iff any object was marked during this traversal (which implies that
** convergence has to continue). During propagation phase, keep table
** in 'grayagain' list, to be visited again in the atomic phase. In
** the atomic phase, if table has any white->white entry, it has to
** be revisited during ephemeron convergence (as that key may turn
** black). Otherwise, if it has any white key, table has to be cleared
** (in the atomic phase). In generational mode, some tables
** must be kept in some gray list for post-processing; this is done
** by 'genlink'.
*/
/*
遍历一个弱key的表并将其链接到适当的列表。
1）先计算数组部分和hash部分的长度
2）遍历数组部分，如果存在白色元素，标记该元素，并设置mark标记
3）遍历hash部分，inv表示倒序遍历
4）如果key为nil，设置key为deadkey
5）如果key是白色，设置hasclears标记，如果值也是白色设置hasww标记
6）如果值是白色，标记该对象，并设置mark标记
7）如果在传播阶段，表h放入garyagain
8）如果存在白-白键值对，表h放入ephemeron
9）如果有hasclears标记，表h放入allweak
10）调用genlink，判断表h的Age决定是否再扫描它
*/
static int traverseephemeron (global_State *g, Table *h, int inv) {
  int hasclears = 0;  /* true if table has white keys */
  int hasww = 0;  /* true if table has entry "white-key -> white-value" */
  unsigned int i;
  unsigned int nsize = sizenode(h);
  int marked = traversearray(g, h);  /* traverse array part */
  /* traverse hash part; if 'inv', traverse descending
     (see 'convergeephemerons') */
  for (i = 0; i < nsize; i++) {
    Node *n = inv ? gnode(h, nsize - 1 - i) : gnode(h, i);
    if (isempty(gval(n)))  /* entry is empty? */
      clearkey(n);  /* clear its key */
    else if (iscleared(g, gckeyN(n))) {  /* key is not marked (yet)? */
      hasclears = 1;  /* table must be cleared */
      if (valiswhite(gval(n)))  /* value not marked yet? */
        hasww = 1;  /* white-white entry */
    }
    else if (valiswhite(gval(n))) {  /* value not marked yet? */
      marked = 1;
      reallymarkobject(g, gcvalue(gval(n)));  /* mark it now */
    }
  }
  /* link table into proper list */
  if (g->gcstate == GCSpropagate)
    linkgclist(h, g->grayagain);  /* must retraverse it in atomic phase */
  else if (hasww)  /* table has white->white entries? */
    linkgclist(h, g->ephemeron);  /* have to propagate again */
  else if (hasclears)  /* table has white keys? */
    linkgclist(h, g->allweak);  /* may have to clean white keys */
  else
    genlink(g, obj2gco(h));  /* check whether collector still needs to see it */
  return marked;
}


/*
遍历一个强表并将其链接到适当的列表。
1）计算数组部分的长度，以及最后一个hash元素
2）遍历数组部分，并标记所有元素
3）遍历hash部分，如果key为nil，设置key为deadkey
4）如果key不为nil，标记key和value
5）调用genlink，判断表h的Age决定是否再扫描它
*/
static void traversestrongtable (global_State *g, Table *h) {
  Node *n, *limit = gnodelast(h);
  traversearray(g, h);
  for (n = gnode(h, 0); n < limit; n++) {  /* traverse hash part */
    if (isempty(gval(n)))  /* entry is empty? */
      clearkey(n);  /* clear its key */
    else {
      lua_assert(!keyisnil(n));
      markkey(g, n);
      markvalue(g, gval(n));
    }
  }
  genlink(g, obj2gco(h));
}


/*
遍历一个表并将其链接到适当的列表。
1）先获取表h的元表中mode字段
2）标记表h的元表
3）判断表h的弱表类型执行相关操作
3.1）v：调用traverseweakvalue
3.2）k：调用traverseephemeron
3.3）kv：表放入allweak链表
4）非弱表，调用traversestrongtable
5）返回工作量，1 + array count + 2 * hash count
*/
static void traversetable (global_State *g, Table *h) {
  const char *weakkey, *weakvalue;
  const TValue *mode = gfasttm(g, h->metatable, TM_MODE);
  TString *smode;
  markobjectN(g, h->metatable);
  if (mode && ttisshrstring(mode) &&  /* is there a weak mode? */
      (cast_void(smode = tsvalue(mode)),
       cast_void(weakkey = strchr(getshrstr(smode), 'k')),
       cast_void(weakvalue = strchr(getshrstr(smode), 'v')),
       (weakkey || weakvalue))) {  /* is really weak? */
    if (!weakkey)  /* strong keys? */
      traverseweakvalue(g, h);
    else if (!weakvalue)  /* strong values? */
      traverseephemeron(g, h, 0);
    else  /* all weak */
      linkgclist(h, g->allweak);  /* nothing to traverse now */
  }
  else  /* not weak */
    traversestrongtable(g, h);
}


/*
遍历一个userdata
1）标记u的元表
2）标记u的user values
3）调用genlink，判断表h的Age决定是否再扫描它
4）返回工作量，1 + user values count
*/
static void traverseudata (global_State *g, Udata *u) {
  int i;
  markobjectN(g, u->metatable);  /* mark its metatable */
  for (i = 0; i < u->nuvalue; i++)
    markvalue(g, &u->uv[i].uv);
  genlink(g, obj2gco(u));
}


/*
遍历一个函数proto
1）标记f的source
2）标记f的常量列表k
3）标记f的upvalues
4）标记f的嵌套protos
5）标记f的本地变量locvars
6）返回工作量，1 + constants count + upvalue count + proto count + local count
*/
/*
** Traverse a prototype. (While a prototype is being build, its
** arrays can be larger than needed; the extra slots are filled with
** NULL, so the use of 'markobjectN')
*/
static void traverseproto (global_State *g, Proto *f) {
  int i;
  markobjectN(g, f->source);
  for (i = 0; i < f->sizek; i++)  /* mark literals */
    markvalue(g, &f->k[i]);
  for (i = 0; i < f->sizeupvalues; i++)  /* mark upvalue names */
    markobjectN(g, f->upvalues[i].name);
  for (i = 0; i < f->sizep; i++)  /* mark nested protos */
    markobjectN(g, f->p[i]);
  for (i = 0; i < f->sizelocvars; i++)  /* mark local-variable names */
    markobjectN(g, f->locvars[i].varname);
}


/*
遍历C闭包
1）标记cl的upvalues
2）返回工作量，1 + upvalue count
*/
static void traverseCclosure (global_State *g, CClosure *cl) {
  int i;
  for (i = 0; i < cl->nupvalues; i++)  /* mark its upvalues */
    markvalue(g, &cl->upvalue[i]);
}

/*
遍历lua闭包
1）标记cl的prototype
2）标记cl的upvalues
3）返回工作量，1 + upvalue count
*/
/*
** Traverse a Lua closure, marking its prototype and its upvalues.
** (Both can be NULL while closure is being created.)
*/
static void traverseLclosure (global_State *g, LClosure *cl) {
  int i;
  markobjectN(g, cl->p);  /* mark its prototype */
  for (i = 0; i < cl->nupvalues; i++) {  /* visit its upvalues */
    UpVal *uv = cl->upvals[i];
    markobjectN(g, uv);  /* mark upvalue */
  }
}


/*
遍历thread
1）判断th的age是oid，或者在传播阶段，将th加入grayagain
2）判断th的stack是否创建，为创建则直接返回工作量 1
3）标记th栈上的value
4）标记th中打开的upvalue
5）如果在automic阶段，清空stack上的dead对象，并将th挂到g->twups
6）如果不是紧急收集，则尝试收缩th的堆栈
7）返回工作量，1 + stack size
*/
/*
** Traverse a thread, marking the elements in the stack up to its top
** and cleaning the rest of the stack in the final traversal. That
** ensures that the entire stack have valid (non-dead) objects.
** Threads have no barriers. In gen. mode, old threads must be visited
** at every cycle, because they might point to young objects.  In inc.
** mode, the thread can still be modified before the end of the cycle,
** and therefore it must be visited again in the atomic phase. To ensure
** these visits, threads must return to a gray list if they are not new
** (which can only happen in generational mode) or if the traverse is in
** the propagate phase (which can only happen in incremental mode).
*/
static void traversethread (global_State *g, lua_State *th) {
  UpVal *uv;
  StkId o = th->stack.p;
  if (isold(th) || g->gcstate == GCSpropagate)
    linkgclist(th, g->grayagain);  /* insert into 'grayagain' list */
  if (o == NULL)
    return;  /* stack not completely built yet */
  lua_assert(g->gcstate == GCSatomic ||
             th->openupval == NULL || isintwups(th));
  for (; o < th->top.p; o++)  /* mark live elements in the stack */
    markvalue(g, s2v(o));
  for (uv = th->openupval; uv != NULL; uv = uv->u.open.next)
    markobject(g, uv);  /* open upvalues cannot be collected */
  if (g->gcstate == GCSatomic) {  /* final traversal? */
    if (!g->gcemergency)
      luaD_shrinkstack(th); /* do not change stack in emergency cycle */
    for (o = th->top.p; o < th->stack_last.p + EXTRA_STACK; o++)
      setnilvalue(s2v(o));  /* clear dead stack slice */
    /* 'remarkupvals' may have removed thread from 'twups' list */
    if (!isintwups(th) && th->openupval != NULL) {
      th->twups = g->twups;  /* link it back to the list */
      g->twups = th;
    }
  }
}


/*
传播标记gray的head对象
1）获取g->gray保存到o，并标记为黑色
2）将o从gray移除，并将gray指向下一个对象
3）遍历标记o，并返回工作量
*/
/*
** traverse one gray object, turning it to black.
*/
static void propagatemark (global_State *g) {
  GCObject *o = g->gray;
  nw2black(o);
  g->gray = *getgclist(o);  /* remove from 'gray' list */
  switch (o->tt) {
    case LUA_VTABLE: traversetable(g, gco2t(o)); break;
    case LUA_VUSERDATA: traverseudata(g, gco2u(o)); break;
    case LUA_VLCL: traverseLclosure(g, gco2lcl(o)); break;
    case LUA_VCCL: traverseCclosure(g, gco2ccl(o)); break;
    case LUA_VPROTO: traverseproto(g, gco2p(o)); break;
    case LUA_VTHREAD: traversethread(g, gco2th(o)); break;
    default: lua_assert(0);
  }
}


// 遍历gary列表，并计算work
static l_obj propagateall (global_State *g) {
  l_obj work = 0;
  while (g->gray) {
    propagatemark(g);
    work++;
  }
  return work;
}


/*
集中处理ephemeron表
1）遍历g->ephemeron
2）将遍历到的表元素标记为黑色，并遍历该表元素的子元素
3）如果标记成功则标记changed
4）标记成功遍历一次graylist
5）未标记成功则反向遍历一次，直到无法标记changed
*/
/*
** Traverse all ephemeron tables propagating marks from keys to values.
** Repeat until it converges, that is, nothing new is marked. 'dir'
** inverts the direction of the traversals, trying to speed up
** convergence on chains in the same table.
*/
static l_obj convergeephemerons (global_State *g) {
  int changed;
  l_obj work = 0;
  int dir = 0;
  do {
    GCObject *w;
    GCObject *next = g->ephemeron;  /* get ephemeron list */
    g->ephemeron = NULL;  /* tables may return to this list when traversed */
    changed = 0;
    while ((w = next) != NULL) {  /* for each ephemeron table */
      Table *h = gco2t(w);
      next = h->gclist;  /* list is rebuilt during loop */
      nw2black(h);  /* out of the list (for now) */
      if (traverseephemeron(g, h, dir)) {  /* marked some value? */
        propagateall(g);  /* propagate changes */
        changed = 1;  /* will have to revisit all ephemeron tables */
      }
      work++;
    }
    dir = !dir;  /* invert direction next time */
  } while (changed);  /* repeat until no more changes */
  return work;
}

/* }====================================================== */


/*
** {======================================================
** Sweep Functions
** =======================================================
*/


/*
清除列表l中的所有弱表的未标记的keys
1）遍历列表l的gclist中的所有表
2）找到表h的最后一个hash元素，遍历表h
3）如果该键值对的key未标记，则将value设置未空
4）如果该键值对的value为空，则清除该key
*/
/*
** clear entries with unmarked keys from all weaktables in list 'l'
*/
static l_obj clearbykeys (global_State *g, GCObject *l) {
  l_obj work = 0;
  for (; l; l = gco2t(l)->gclist) {
    Table *h = gco2t(l);
    Node *limit = gnodelast(h);
    Node *n;
    for (n = gnode(h, 0); n < limit; n++) {
      if (iscleared(g, gckeyN(n)))  /* unmarked key? */
        setempty(gval(n));  /* remove entry */
      if (isempty(gval(n)))  /* is entry empty? */
        clearkey(n);  /* clear its key */
    }
    work++;
  }
  return work;
}


/*
清除列表l中的所有弱表的未标记的values,直到遇到元素f为止
1）遍历列表l的gclist中的所有表
2）获取表h的最后一个hash元素limit和array的长度
3）遍历表h的array部分，如果值未标记，则将value设置未空
4）找到表h的最后一个hash元素，遍历表h
5）遍历表h的hash部分，如果该键值对的value未标记，则将value设置未空
6）如果该键值对的value为空，则清除该key
*/
/*
** clear entries with unmarked values from all weaktables in list 'l' up
** to element 'f'
*/
static l_obj clearbyvalues (global_State *g, GCObject *l, GCObject *f) {
  l_obj work = 0;
  for (; l != f; l = gco2t(l)->gclist) {
    Table *h = gco2t(l);
    Node *n, *limit = gnodelast(h);
    unsigned int i;
    unsigned int asize = luaH_realasize(h);
    for (i = 0; i < asize; i++) {
      GCObject *o = gcvalarr(h, i);
      if (iscleared(g, o))  /* value was collected? */
        *getArrTag(h, i) = LUA_VEMPTY;  /* remove entry */
    }
    for (n = gnode(h, 0); n < limit; n++) {
      if (iscleared(g, gcvalueN(gval(n))))  /* unmarked value? */
        setempty(gval(n));  /* remove entry */
      if (isempty(gval(n)))  /* is entry empty? */
        clearkey(n);  /* clear its key */
    }
    work++;
  }
  return work;
}


/*
释放upvalue
1）如果uv是打开的，unlink这个uv对象
2）释放uv对象的内存
*/
static void freeupval (lua_State *L, UpVal *uv) {
  if (upisopen(uv))
    luaF_unlinkupval(uv);
  luaM_free(L, uv);
}


/*
释放一个GCObject
1）switch对象类型
2）调用对应的释放接口
*/
static void freeobj (lua_State *L, GCObject *o) {
  G(L)->totalobjs--;
  switch (o->tt) {
    case LUA_VPROTO:
      luaF_freeproto(L, gco2p(o));
      break;
    case LUA_VUPVAL:
      freeupval(L, gco2upv(o));
      break;
    case LUA_VLCL: {
      LClosure *cl = gco2lcl(o);
      luaM_freemem(L, cl, sizeLclosure(cl->nupvalues));
      break;
    }
    case LUA_VCCL: {
      CClosure *cl = gco2ccl(o);
      luaM_freemem(L, cl, sizeCclosure(cl->nupvalues));
      break;
    }
    case LUA_VTABLE:
      luaH_free(L, gco2t(o));
      break;
    case LUA_VTHREAD:
      luaE_freethread(L, gco2th(o));
      break;
    case LUA_VUSERDATA: {
      Udata *u = gco2u(o);
      luaM_freemem(L, o, sizeudata(u->nuvalue, u->len));
      break;
    }
    case LUA_VSHRSTR: {
      TString *ts = gco2ts(o);
      luaS_remove(L, ts);  /* remove it from hash table */
      luaM_freemem(L, ts, sizestrshr(ts->shrlen));
      break;
    }
    case LUA_VLNGSTR: {
      TString *ts = gco2ts(o);
      if (ts->shrlen == LSTRMEM)  /* must free external string? */
        (*ts->falloc)(ts->ud, ts->contents, ts->u.lnglen + 1, 0);
      luaM_freemem(L, ts, luaS_sizelngstr(ts->u.lnglen, ts->shrlen));
      break;
    }
    default: lua_assert(0);
  }
}


/*
扫描一个列表
1）计算当前ow（非白色）和white（白色）
2）遍历链表p中的前countin个对象
3）如果当前对象标记死亡，释放改对象
4）标记该对象
5）计算标记的对象个数
*/
/*
** sweep at most 'countin' elements from a list of GCObjects erasing dead
** objects, where a dead object is one marked with the old (non current)
** white; change all non-dead objects back to white (and new), preparing
** for next collection cycle. Return where to continue the traversal or
** NULL if list is finished.
*/
static GCObject **sweeplist (lua_State *L, GCObject **p, l_obj countin) {
  global_State *g = G(L);
  int ow = otherwhite(g);
  l_obj i;
  int white = luaC_white(g);  /* current white */
  for (i = 0; *p != NULL && i < countin; i++) {
    GCObject *curr = *p;
    int marked = curr->marked;
    if (isdeadm(ow, marked)) {  /* is 'curr' dead? */
      *p = curr->next;  /* remove 'curr' from list */
      freeobj(L, curr);  /* erase 'curr' */
    }
    else {  /* change mark to 'white' and age to 'new' */
      curr->marked = cast_byte((marked & ~maskgcbits) | white | G_NEW);
      p = &curr->next;  /* go to next element */
    }
  }
  return (*p == NULL) ? NULL : p;
}


/*
** sweep a list until a live object (or end of list)
*/
/*
扫描一个列表
1）每次从链表p里取出一个对象进行扫描
2）对象为live或者遍历完返回该对象
*/
static GCObject **sweeptolive (lua_State *L, GCObject **p) {
  GCObject **old = p;
  do {
    p = sweeplist(L, p, 1);
  } while (p == old);
  return p;
}

/* }====================================================== */


/*
** {======================================================
** Finalization
** =======================================================
*/

/*
** If possible, shrink string table.
*/
/*
检查string table的尺寸
1）不是gcemergency
2）string table的使用量小于总量的1/4，将strt的尺寸缩小到当前的1/2
3）回收内存，重新计算GCestimate和GCdebt
*/
static void checkSizes (lua_State *L, global_State *g) {
  if (!g->gcemergency) {
    if (g->strt.nuse < g->strt.size / 4)  /* string table too big? */
      luaS_resize(L, g->strt.size / 2);
  }
}


/*
** Get the next udata to be finalized from the 'tobefnz' list, and
** link it back into the 'allgc' list.
*/
/*
将tobefnz列表中的udata取出放进allgc列表
 1）从tobefnz中取出一个对象
 2）将该对象放到allgc的头部
 3）将该对象标记为FINALIZEDBIT
 4）如果在sweep阶段，设置为白色
 5）如果对象o的age是OLD1，将该对象赋值给firstold1
*/
static GCObject *udata2finalize (global_State *g) {
  GCObject *o = g->tobefnz;  /* get first element */
  lua_assert(tofinalize(o));
  g->tobefnz = o->next;  /* remove it from 'tobefnz' list */
  o->next = g->allgc;  /* return it to 'allgc' list */
  g->allgc = o;
  resetbit(o->marked, FINALIZEDBIT);  /* object is "normal" again */
  if (issweepphase(g))
    makewhite(g, o);  /* "sweep" object */
  else if (getage(o) == G_OLD1)
    g->firstold1 = o;  /* it is the first OLD1 object in the list */
  return o;
}


// 执行ud的__gc方法
static void dothecall (lua_State *L, void *ud) {
  UNUSED(ud);
  luaD_callnoyield(L, L->top.p - 2, 0);
}


/*
执行一个userdata的__gc方法
1）从tobefnz中找到一个对象
2）查询该对象的__gc元方法
3）保存luaState的状态
4）压入方法和对象，执行__gc函数
5）恢复luaState的状态
6）处理错误信息
*/
static void GCTM (lua_State *L) {
  global_State *g = G(L);
  const TValue *tm;
  TValue v;
  lua_assert(!g->gcemergency);
  setgcovalue(L, &v, udata2finalize(g));
  tm = luaT_gettmbyobj(L, &v, TM_GC);
  if (!notm(tm)) {  /* is there a finalizer? */
    int status;
    lu_byte oldah = L->allowhook;
    int oldgcstp  = g->gcstp;
    g->gcstp |= GCSTPGC;  /* avoid GC steps */
    L->allowhook = 0;  /* stop debug hooks during GC metamethod */
    setobj2s(L, L->top.p++, tm);  /* push finalizer... */
    setobj2s(L, L->top.p++, &v);  /* ... and its argument */
    L->ci->callstatus |= CIST_FIN;  /* will run a finalizer */
    status = luaD_pcall(L, dothecall, NULL, savestack(L, L->top.p - 2), 0);
    L->ci->callstatus &= ~CIST_FIN;  /* not running a finalizer anymore */
    L->allowhook = oldah;  /* restore hooks */
    g->gcstp = oldgcstp;  /* restore state */
    if (l_unlikely(status != LUA_OK)) {  /* error while running __gc? */
      luaE_warnerror(L, "__gc");
      L->top.p--;  /* pops error object */
    }
  }
}


/*
** call all pending finalizers
*/
// 执行所有的userdata的finalizers
static void callallpendingfinalizers (lua_State *L) {
  global_State *g = G(L);
  while (g->tobefnz)
    GCTM(L);
}


/*
** find last 'next' field in list 'p' list (to add elements in its end)
*/
// 查找链表的tail元素
static GCObject **findlast (GCObject **p) {
  while (*p != NULL)
    p = &(*p)->next;
  return p;
}


/*
** Move all unreachable objects (or 'all' objects) that need
** finalization from list 'finobj' to list 'tobefnz' (to be finalized).
** (Note that objects after 'finobjold1' cannot be white, so they
** don't need to be traversed. In incremental mode, 'finobjold1' is NULL,
** so the whole list is traversed.)
*/
/*
分离tobefnz的对象，将白色对象放到tobefnx
1）找到tobefnx的最后一个对象lastnext（一定是null）
2）遍历finobj列表中的未old对象cur
3）如果cur不是白色，或者不是全部分离，则跳过
4）如果cur在finobjsur表中，则从finobjsur删除
5）从finobj中删除cur
6）将cur放入到tobefnx最后一个元素
*/
static void separatetobefnz (global_State *g, int all) {
  GCObject *curr;
  GCObject **p = &g->finobj;
  GCObject **lastnext = findlast(&g->tobefnz);
  while ((curr = *p) != g->finobjold1) {  /* traverse all finalizable objects */
    lua_assert(tofinalize(curr));
    if (!(iswhite(curr) || all))  /* not being collected? */
      p = &curr->next;  /* don't bother with it */
    else {
      if (curr == g->finobjsur)  /* removing 'finobjsur'? */
        g->finobjsur = curr->next;  /* correct it */
      *p = curr->next;  /* remove 'curr' from 'finobj' list */
      curr->next = *lastnext;  /* link at the end of 'tobefnz' list */
      *lastnext = curr;
      lastnext = &curr->next;
    }
  }
}


/*
** If pointer 'p' points to 'o', move it to the next element.
*/
// 如果p指向o, p执行p的next，相当于如果o在p的head，删除o对象
static void checkpointer (GCObject **p, GCObject *o) {
  if (o == *p)
    *p = o->next;
}


/*
** Correct pointers to objects inside 'allgc' list when
** object 'o' is being removed from the list.
*/
// 删除相关队列中的o对象
static void correctpointers (global_State *g, GCObject *o) {
  checkpointer(&g->survival, o);
  checkpointer(&g->old1, o);
  checkpointer(&g->reallyold, o);
  checkpointer(&g->firstold1, o);
}


/*
** if object 'o' has a finalizer, remove it from 'allgc' list (must
** search the list to find it) and link it in 'finobj' list.
*/

/*
检查userdata的终结器
1）如果o已经被标记或者没有__gc函数，直接返回
2）如果在扫描阶段，标记o为白色，并检查sweepgc，找到下一个live对象
3）不在扫描阶段，从相关队列删除o
4）从allgc中找到它，并删除
5）将该对象放进finobj列表
6）标记o为FINALIZEDBIT
*/
void luaC_checkfinalizer (lua_State *L, GCObject *o, Table *mt) {
  global_State *g = G(L);
  if (tofinalize(o) ||                 /* obj. is already marked... */
      gfasttm(g, mt, TM_GC) == NULL ||    /* or has no finalizer... */
      (g->gcstp & GCSTPCLS))                   /* or closing state? */
    return;  /* nothing to be done */
  else {  /* move 'o' to 'finobj' list */
    GCObject **p;
    if (issweepphase(g)) {
      makewhite(g, o);  /* "sweep" object 'o' */
      if (g->sweepgc == &o->next)  /* should not remove 'sweepgc' object */
        g->sweepgc = sweeptolive(L, g->sweepgc);  /* change 'sweepgc' */
    }
    else
      correctpointers(g, o);
    /* search for pointer pointing to 'o' */
    for (p = &g->allgc; *p != o; p = &(*p)->next) { /* empty */ }
    *p = o->next;  /* remove 'o' from 'allgc' list */
    o->next = g->finobj;  /* link it in 'finobj' list */
    g->finobj = o;
    l_setbit(o->marked, FINALIZEDBIT);  /* mark it as such */
  }
}

/* }====================================================== */


/*
** {======================================================
** Generational Collector
** =======================================================
*/


/*
** Set the "time" to wait before starting a new incremental cycle;
** cycle will start when number of objects in use hits the threshold of
** approximately (marked * pause / 100).
*/
/*
进入暂停状态，等待time之后进行一次新的GC循环
1）获取gc的pause参数
2）计算estimate
3）计算债务阈值threshold
4）计算债务debt并设置
*/
static void setpause (global_State *g) {
  l_obj threshold = applygcparam(g, PAUSE, g->marked);
  l_obj debt = threshold - gettotalobjs(g);
  if (debt < 0) debt = 0;
//printf("pause: %ld  %ld\n", debt, g->marked);
  luaE_setdebt(g, debt);
}


/*
** Sweep a list of objects to enter generational mode.  Deletes dead
** objects and turns the non dead to old. All non-dead threads---which
** are now old---must be in a gray list. Everything else is not in a
** gray list. Open upvalues are also kept gray.
*/
/*
分代模式扫描对象列表p，然后将所有对象变为old
1）遍历对象列表p
2）如果对象是白色，那么是否该对象
3）如果不是白色，那么标记它的Age为old
4）如果对象是thread，将他放进grayagain
5）如果对手是upvalue并且没有关闭，标记为灰色
6）其他则标记为黑色
*/
static void sweep2old (lua_State *L, GCObject **p) {
  GCObject *curr;
  global_State *g = G(L);
  while ((curr = *p) != NULL) {
    if (iswhite(curr)) {  /* is 'curr' dead? */
      lua_assert(isdead(g, curr));
      *p = curr->next;  /* remove 'curr' from list */
      freeobj(L, curr);  /* erase 'curr' */
    }
    else {  /* all surviving objects become old */
      setage(curr, G_OLD);
      if (curr->tt == LUA_VTHREAD) {  /* threads must be watched */
        lua_State *th = gco2th(curr);
        linkgclist(th, g->grayagain);  /* insert into 'grayagain' list */
      }
      else if (curr->tt == LUA_VUPVAL && upisopen(gco2upv(curr)))
        set2gray(curr);  /* open upvalues are always gray */
      else  /* everything else is black */
        nw2black(curr);
      p = &curr->next;  /* go to next element */
    }
  }
}


/*
** Sweep for generational mode. Delete dead objects. (Because the
** collection is not incremental, there are no "new white" objects
** during the sweep. So, any white object must be dead.) For
** non-dead objects, advance their ages and clear the color of
** new objects. (Old objects keep their colors.)
** The ages of G_TOUCHED1 and G_TOUCHED2 objects cannot be advanced
** here, because these old-generation objects are usually not swept
** here.  They will all be advanced in 'correctgraylist'. That function
** will also remove objects turned white here from any gray list.
*/
/*
分代模式清理队列p，直到limit对象
1）遍历队列p，直到遇到limit
2）如果对象是白色，则释放该对象
3）如果不是白色，Age为NEW，设置它的age为G_SURVIVAL，并标记为白色
4）如果不是NEW，则设置age为next age
5）如果AGE为OLD1，并且pfirstold1为空，则设置pfirstold1
*/
static GCObject **sweepgen (lua_State *L, global_State *g, GCObject **p,
                            GCObject *limit, GCObject **pfirstold1,
                            l_obj *paddedold) {
  static const lu_byte nextage[] = {
    G_SURVIVAL,  /* from G_NEW */
    G_OLD1,      /* from G_SURVIVAL */
    G_OLD1,      /* from G_OLD0 */
    G_OLD,       /* from G_OLD1 */
    G_OLD,       /* from G_OLD (do not change) */
    G_TOUCHED1,  /* from G_TOUCHED1 (do not change) */
    G_TOUCHED2   /* from G_TOUCHED2 (do not change) */
  };
  l_obj addedold = 0;
  int white = luaC_white(g);
  GCObject *curr;
  while ((curr = *p) != limit) {
    if (iswhite(curr)) {  /* is 'curr' dead? */
      lua_assert(!isold(curr) && isdead(g, curr));
      *p = curr->next;  /* remove 'curr' from list */
      freeobj(L, curr);  /* erase 'curr' */
    }
    else {  /* correct mark and age */
      int age = getage(curr);
      if (age == G_NEW) {  /* new objects go back to white */
        int marked = curr->marked & ~maskgcbits;  /* erase GC bits */
        curr->marked = cast_byte(marked | G_SURVIVAL | white);
      }
      else {  /* all other objects will be old, and so keep their color */
        lua_assert(age != G_OLD1);  /* advanced in 'markold' */
        setage(curr, nextage[age]);
        if (getage(curr) == G_OLD1) {
          addedold++;  /* one more object becoming old */
          if (*pfirstold1 == NULL)
            *pfirstold1 = curr;  /* first OLD1 object in the list */
        }
      }
      p = &curr->next;  /* go to next element */
    }
  }
  *paddedold += addedold;
  return p;
}


/*
** Correct a list of gray objects. Return a pointer to the last element
** left on the list, so that we can link another list to the end of
** this one.
** Because this correction is done after sweeping, young objects might
** be turned white and still be in the list. They are only removed.
** 'TOUCHED1' objects are advanced to 'TOUCHED2' and remain on the list;
** Non-white threads also remain on the list. 'TOUCHED2' objects and
** anything else become regular old, are marked black, and are removed
** from the list.
*/
/*
修正灰色列表p
1）遍历列表p
2）获取cur对象的gclist
3）如果是白色，从列表p中删除cur
4）如果age为G_TOUCHED1，标记为黑色，并设置age为G_TOUCHED2
5）如果cur是thread，不做任何处理
6）如果不是thread，标记为黑色，如age为G_TOUCHED2，设置age为OLD
*/
static GCObject **correctgraylist (GCObject **p) {
  GCObject *curr;
  while ((curr = *p) != NULL) {
    GCObject **next = getgclist(curr);
    if (iswhite(curr))
      goto remove;  /* remove all white objects */
    else if (getage(curr) == G_TOUCHED1) {  /* touched in this cycle? */
      lua_assert(isgray(curr));
      nw2black(curr);  /* make it black, for next barrier */
      setage(curr, G_TOUCHED2);
      goto remain;  /* keep it in the list and go to next element */
    }
    else if (curr->tt == LUA_VTHREAD) {
      lua_assert(isgray(curr));
      goto remain;  /* keep non-white threads on the list */
    }
    else {  /* everything else is removed */
      lua_assert(isold(curr));  /* young objects should be white here */
      if (getage(curr) == G_TOUCHED2)  /* advance from TOUCHED2... */
        setage(curr, G_OLD);  /* ... to OLD */
      nw2black(curr);  /* make object black (to be removed) */
      goto remove;
    }
    remove: *p = *next; continue;
    remain: p = next; continue;
  }
  return p;
}


/*
** Correct all gray lists, coalescing them into 'grayagain'.
*/
/*
修正所有的灰色表，合并到grayagain
1）先修正grayagain
2）修正weak，合并到grayagain
3）修正allweak，合并到grayagain
4）修正ephemeron，合并到grayagain
*/
static void correctgraylists (global_State *g) {
  GCObject **list = correctgraylist(&g->grayagain);
  *list = g->weak; g->weak = NULL;
  list = correctgraylist(list);
  *list = g->allweak; g->allweak = NULL;
  list = correctgraylist(list);
  *list = g->ephemeron; g->ephemeron = NULL;
  correctgraylist(list);
}


/*
** Mark black 'OLD1' objects when starting a new young collection.
** Gray objects are already in some gray list, and so will be visited in
** the atomic step.
*/
/*
将from到to的old1状态的对象标记old
1）遍历从from到to的对象
2）如果对象age为old1,标记为old
3）如果之前是黑色，则重新标记对象
*/
static void markold (global_State *g, GCObject *from, GCObject *to) {
  GCObject *p;
  for (p = from; p != to; p = p->next) {
    if (getage(p) == G_OLD1) {
      lua_assert(!iswhite(p));
      setage(p, G_OLD);  /* now they are old */
      if (isblack(p))
        reallymarkobject(g, p);
    }
  }
}


/*
** Finish a young-generation collection.
*/
/*
结束一次young分代收集
1）修正所有的graylist
2）检查字符串表，看能否收缩
3）设置状态为GCSpropagate
4）不是紧急gc则处理所有待定的finalizer
*/
static void finishgencycle (lua_State *L, global_State *g) {
  correctgraylists(g);
  checkSizes(L, g);
  g->gcstate = GCSpropagate;  /* skip restart */
  if (!g->gcemergency)
    callallpendingfinalizers(L);
}


/*
** Shifts from a minor collection to major collections. It starts in
** the "sweep all" state to clear all objects, which are mostly black
** in generational mode.
*/
static void minor2inc (lua_State *L, global_State *g, int kind) {
  g->GCmajorminor = g->marked;  /* number of live objects */
  g->gckind = kind;
  g->reallyold = g->old1 = g->survival = NULL;
  g->finobjrold = g->finobjold1 = g->finobjsur = NULL;
  entersweep(L);  /* continue as an incremental cycle */
  /* set a debt equal to the step size */
  luaE_setdebt(g, applygcparam(g, STEPSIZE, 100));
}


/*
** Decide whether to shift to major mode. It tests two conditions:
** 1) Whether the number of added old objects in this collection is more
** than half the number of new objects. ('step' is the number of objects
** created between minor collections. Except for forward barriers, it
** is the maximum number of objects that can become old in each minor
** collection.)
** 2) Whether the accumulated number of added old objects is larger
** than 'minormajor'% of the number of lived objects after the last
** major collection. (That percentage is computed in 'limit'.)
*/
static int checkminormajor (global_State *g, l_obj addedold1) {
  l_obj step = applygcparam(g, MINORMUL, g->GCmajorminor);
  l_obj limit = applygcparam(g, MINORMAJOR, g->GCmajorminor);
//printf("-> (%ld) major? marked: %ld  limit: %ld  step: %ld  addedold1: %ld)\n", gettotalobjs(g), g->marked, limit, step, addedold1);
  return (addedold1 >= (step >> 1) || g->marked >= limit);
}

/*
** Does a young collection. First, mark 'OLD1' objects. Then does the
** atomic step. Then, check whether to continue in minor mode. If so,
** sweep all lists and advance pointers. Finally, finish the collection.
*/
/*
执行一次young分代收集
1）检查本次扫描的firstold1，将firstold1到上次扫描的reallyold之间的对象都标记为old
2）将finobj到上次扫描的finobjrold之间的对象都标记为old
3）将所有tobefnz的对象标记为old
4）执行一次原子处理
5）进入GCSswpallgc状态
6）扫描allgc，将所有new对象标记为survival，并记录firstobj对象
7）扫描survival，将所有survival对象变老一个状态，并记录firstobj对象
8）更新old1，reallyold，survival链表的位置
10）扫描finobj，将所有new对象标记为survival，并记录仿firstobj对象dummy
11）扫描finobjsur，将所有survival对象变老一个状态，并记录仿firstobj对象dummy
12）更新finobjold1，finobjrold，finobjsur链表的位置
13）扫描tobefnz
14）完成一次young分代
*/
static void youngcollection (lua_State *L, global_State *g) {
  l_obj addedold1 = 0;
  l_obj marked = g->marked;  /* preserve 'g->marked' */
  GCObject **psurvival;  /* to point to first non-dead survival object */
  GCObject *dummy;  /* dummy out parameter to 'sweepgen' */
  lua_assert(g->gcstate == GCSpropagate);
  if (g->firstold1) {  /* are there regular OLD1 objects? */
    markold(g, g->firstold1, g->reallyold);  /* mark them */
    g->firstold1 = NULL;  /* no more OLD1 objects (for now) */
  }
  markold(g, g->finobj, g->finobjrold);
  markold(g, g->tobefnz, NULL);

  atomic(L);  /* will lose 'g->marked' */

  /* sweep nursery and get a pointer to its last live element */
  g->gcstate = GCSswpallgc;
  psurvival = sweepgen(L, g, &g->allgc, g->survival, &g->firstold1, &addedold1);
  /* sweep 'survival' */
  sweepgen(L, g, psurvival, g->old1, &g->firstold1, &addedold1);
  g->reallyold = g->old1;
  g->old1 = *psurvival;  /* 'survival' survivals are old now */
  g->survival = g->allgc;  /* all news are survivals */

  /* repeat for 'finobj' lists */
  dummy = NULL;  /* no 'firstold1' optimization for 'finobj' lists */
  psurvival = sweepgen(L, g, &g->finobj, g->finobjsur, &dummy, &addedold1);
  /* sweep 'survival' */
  sweepgen(L, g, psurvival, g->finobjold1, &dummy, &addedold1);
  g->finobjrold = g->finobjold1;
  g->finobjold1 = *psurvival;  /* 'survival' survivals are old now */
  g->finobjsur = g->finobj;  /* all news are survivals */

  sweepgen(L, g, &g->tobefnz, NULL, &dummy, &addedold1);

  /* keep total number of added old1 objects */
  g->marked = marked + addedold1;

  /* decide whether to shift to major mode */
  if (checkminormajor(g, addedold1)) {
    minor2inc(L, g, KGC_GENMAJOR);  /* go to major mode */
    g->marked = 0;  /* avoid pause in first major cycle */
  }
  else
    finishgencycle(L, g);  /* still in minor mode; finish it */
}


/*
** Clears all gray lists, sweeps objects, and prepare sublists to enter
** generational mode. The sweeps remove dead objects and turn all
** surviving objects to old. Threads go back to 'grayagain'; everything
** else is turned black (not in any gray list).
*/
/*
原子操作进入分代模式
1）清理graylist，进入GCSswpallgc阶段
2）扫描所有的old对象，并将所有的allgc对象设置为old
3）扫描finobj，并将所有的finobj对象设置为old
4）扫描tobefnz，并将所有的tobefnz对象设置为old
5）返回分代模式，结束一次循环
*/
static void atomic2gen (lua_State *L, global_State *g) {
  cleargraylists(g);
  /* sweep all elements making them old */
  g->gcstate = GCSswpallgc;
  sweep2old(L, &g->allgc);
  /* everything alive now is old */
  g->reallyold = g->old1 = g->survival = g->allgc;
  g->firstold1 = NULL;  /* there are no OLD1 objects anywhere */

  /* repeat for 'finobj' lists */
  sweep2old(L, &g->finobj);
  g->finobjrold = g->finobjold1 = g->finobjsur = g->finobj;

  sweep2old(L, &g->tobefnz);

  g->gckind = KGC_GENMINOR;
  g->GCmajorminor = g->marked;  /* "base" for number of objects */
  g->marked = 0;  /* to count the number of added old1 objects */
  finishgencycle(L, g);
}


/*
** Set debt for the next minor collection, which will happen when
** total number of objects grows 'genminormul'%.
*/
/*
设置下一个小分代循环的债务
debt = -当前使用内存 / 100 * genminormul
*/
static void setminordebt (global_State *g) {
  luaE_setdebt(g, applygcparam(g, MINORMUL, g->GCmajorminor));
}


/*
进入分代GC模式
必须持续一个原子循环确保所有对象都已正确标记，并在表中显示都被清除了，然后将所有对象变为旧对象并完成收集
1）等待GCSpause准备进入一次新的cycle
2）等待GCSpropagate
3）执行atomic标记工作
4）执行一次原子收集并进入分代模式
*/
/*
** Enter generational mode. Must go until the end of an atomic cycle
** to ensure that all objects are correctly marked and weak tables
** are cleared. Then, turn all objects into old and finishes the
** collection.
*/
static void entergen (lua_State *L, global_State *g) {
  luaC_runtilstate(L, GCSpause, 1);  /* prepare to start a new cycle */
  luaC_runtilstate(L, GCSpropagate, 1);  /* start new cycle */
  atomic(L);  /* propagates all and then do the atomic stuff */
  atomic2gen(L, g);
  setminordebt(g);  /* set debt assuming next cycle will be minor */
}


/*
** Change collector mode to 'newmode'.
*/
// 改变GC模式，初始化是INC模式
void luaC_changemode (lua_State *L, int newmode) {
  global_State *g = G(L);
  if (g->gckind == KGC_GENMAJOR)  /* doing major collections? */
    g->gckind = KGC_INC;  /* already incremental but in name */
  if (newmode != g->gckind) {  /* does it need to change? */
    if (newmode == KGC_INC)  /* entering incremental mode? */
      minor2inc(L, g, KGC_INC);  /* entering incremental mode */
    else {
      lua_assert(newmode == KGC_GENMINOR);
      entergen(L, g);
    }
  }
}


/*
执行一次全量分代GC
1）调用enterinc，这里只是利用这个接口标记所有对象的状态
2）执行entergen，执行分代全量gc
*/
/*
** Does a full collection in generational mode.
*/
static void fullgen (lua_State *L, global_State *g) {
  minor2inc(L, g, KGC_INC);
  entergen(L, g);
}


/*
执行一次单步分代全量GC
1）确保切换到INC模式
2）执行GC直到达到GCSpropagate
3）mark所有对象
4）达到要求，返回分代模式，并设置小分代债务
5）开始扫描，直到GCSpause
6）setpause完成一次gc循环
*/
/*
** After an atomic incremental step from a major collection,
** check whether collector could return to minor collections.
** It checks whether the number of objects 'tobecollected'
** is greater than 'majorminor'% of the number of objects added
** since the last collection ('addedobjs').
*/
static int checkmajorminor (lua_State *L, global_State *g) {
  if (g->gckind == KGC_GENMAJOR) {  /* generational mode? */
    l_obj numobjs = gettotalobjs(g);
    l_obj addedobjs = numobjs - g->GCmajorminor;
    l_obj limit = applygcparam(g, MAJORMINOR, addedobjs);
    l_obj tobecollected = numobjs - g->marked;
//printf("(%ld) -> minor? tobecollected: %ld  limit: %ld\n", numobjs, tobecollected, limit);
    if (tobecollected > limit) {
      atomic2gen(L, g);  /* return to generational mode */
      setminordebt(g);
      return 0;  /* exit incremental collection */
    }
  }
  g->GCmajorminor = g->marked;  /* prepare for next collection */
  return 1;  /* stay doing incremental collections */
}

/* }====================================================== */


/*
** {======================================================
** GC control
** =======================================================
*/


/*
** Enter first sweep phase.
** The call to 'sweeptolive' makes the pointer point to an object
** inside the list (instead of to the header), so that the real sweep do
** not need to skip objects created between "now" and the start of the
** real sweep.
*/
/*
进入GCSswpallgc状态
1）设置GCSswpallgc状态
2）设置sweepgc对象
*/
static void entersweep (lua_State *L) {
  global_State *g = G(L);
  g->gcstate = GCSswpallgc;
  lua_assert(g->sweepgc == NULL);
  g->sweepgc = sweeptolive(L, &g->allgc);
}


/*
** Delete all objects in list 'p' until (but not including) object
** 'limit'.
*/
// 从链表P中释放对象，直到遍历到对象limit
static void deletelist (lua_State *L, GCObject *p, GCObject *limit) {
  while (p != limit) {
    GCObject *next = p->next;
    freeobj(L, p);
    p = next;
  }
}


/*
** Call all finalizers of the objects in the given Lua state, and
** then free all objects, except for the main thread.
*/
/*
删除所有的对象（除了main thread）
1）切换到INC模式
2）分离tobefnz对象，将finobj里面的白色放到tobefnz
3）执行所有的userdata的__gc函数，即清除tobefnz的对象
4）依次删除allgc，finobj，fixedgc的对象
*/
void luaC_freeallobjects (lua_State *L) {
  global_State *g = G(L);
  g->gcstp = GCSTPCLS;  /* no extra finalizers after here */
  luaC_changemode(L, KGC_INC);
  separatetobefnz(g, 1);  /* separate all objects with finalizers */
  lua_assert(g->finobj == NULL);
  callallpendingfinalizers(L);
  deletelist(L, g->allgc, obj2gco(g->mainthread));
  lua_assert(g->finobj == NULL);  /* no new finalizers */
  deletelist(L, g->fixedgc, NULL);  /* collect fixed objects */
  lua_assert(g->strt.nuse == 0);
}

/*
执行一次原子扫描
1）设置状态GCSatomic，保存grayagain
2）标记mainthread、l_registry、全局metatables等全局数据
3）标记gray列表
4）重新标记upvalues
5）将grayagain赋值给gray，再次标记gray列表
6）集中处理ephemerons
7）清除weak和allweak中的失效的值
8）分离finobj列表，将白色对象放入tobefnz
9）标记tobefnz
10）再次标记gray列表
11）集中处理ephemerons
12）清除ephemeron和allweak中的失效的key
13）清除weak和allweak中的失效的值
14）清除字符串缓存中的白色字符串
15）翻转current_white
*/
static l_obj atomic (lua_State *L) {
  l_obj work = 0;
  global_State *g = G(L);
  GCObject *origweak, *origall;
  GCObject *grayagain = g->grayagain;  /* save original list */
  g->grayagain = NULL;
  lua_assert(g->ephemeron == NULL && g->weak == NULL);
  lua_assert(!iswhite(g->mainthread));
  g->gcstate = GCSatomic;
  markobject(g, L);  /* mark running thread */
  /* registry and global metatables may be changed by API */
  markvalue(g, &g->l_registry);
  markmt(g);  /* mark global metatables */
  work += propagateall(g);  /* empties 'gray' list */
  /* remark occasional upvalues of (maybe) dead threads */
  work += remarkupvals(g);
  work += propagateall(g);  /* propagate changes */
  g->gray = grayagain;
  work += propagateall(g);  /* traverse 'grayagain' list */
  work += convergeephemerons(g);
  /* at this point, all strongly accessible objects are marked. */
  /* Clear values from weak tables, before checking finalizers */
  work += clearbyvalues(g, g->weak, NULL);
  work += clearbyvalues(g, g->allweak, NULL);
  origweak = g->weak; origall = g->allweak;
  separatetobefnz(g, 0);  /* separate objects to be finalized */
  work += markbeingfnz(g);  /* mark objects that will be finalized */
  work += propagateall(g);  /* remark, to propagate 'resurrection' */
  work += convergeephemerons(g);
  /* at this point, all resurrected objects are marked. */
  /* remove dead objects from weak tables */
  work += clearbykeys(g, g->ephemeron);  /* clear keys from all ephemeron */
  work += clearbykeys(g, g->allweak);  /* clear keys from all 'allweak' */
  /* clear values from resurrected weak tables */
  work += clearbyvalues(g, g->weak, origweak);
  work += clearbyvalues(g, g->allweak, origall);
  luaS_clearcache(g);
  g->currentwhite = cast_byte(otherwhite(g));  /* flip current white */
  lua_assert(g->gray == NULL);
  return work;
}


/*
进行一次扫描
1）判断sweepgc是否存在
2）如果存在，则记录扫描sweepgc的work，并评估GCestimate
3）如果不存在，则进入下一个状态，并设置sweepgc为下一条链表（如果有）的head
*/
/*
** Do a sweep step. The normal case (not fast) sweeps at most GCSWEEPMAX
** elements. The fast case sweeps the whole list.
*/
static void sweepstep (lua_State *L, global_State *g,
                       int nextstate, GCObject **nextlist, int fast) {
  if (g->sweepgc)
    g->sweepgc = sweeplist(L, g->sweepgc, fast ? MAX_LOBJ : GCSWEEPMAX);
  else {  /* enter next state */
    g->gcstate = nextstate;
    g->sweepgc = nextlist;
  }
}


/*
根据当前状态执行一次单元收集
1）GCSpause（不可拆分），启动一轮新的回收
2）GCSpropagate（可拆分），从gray链表中拿出头部obj，traverse该obj
3）GCSenteratomic（不可拆分），用来确保mark已经全部完成
4）GCSswpallgc（可拆分），扫描allgc链表
5）GCSswpfinobj（可拆分），扫描finobj链表
6）GCSswptobefnz（可拆分），扫描tobefnz链表
7）GCSswpend（不可拆分），扫描完成，检查string table
8）GCScallfin（可拆分），完成一次GC过程
*/
/*
** Performs one incremental "step" in an incremental garbage collection.
** For indivisible work, a step goes to the next state. When marking
** (propagating), a step traverses one object. When sweeping, a step
** sweeps GCSWEEPMAX objects, to avoid a big overhead for sweeping
** objects one by one. (Sweeping is inexpensive, no matter the
** object.) When 'fast' is true, 'singlestep' tries to finish a state
** "as fast as possible". In particular, it skips the propagation
** phase and leaves all objects to be traversed by the atomic phase:
** That avoids traversing twice some objects, such as theads and
** weak tables.
*/
static l_obj singlestep (lua_State *L, int fast) {
  global_State *g = G(L);
  l_obj work;
  lua_assert(!g->gcstopem);  /* collector is not reentrant */
  g->gcstopem = 1;  /* no emergency collections while collecting */
  switch (g->gcstate) {
    case GCSpause: {
      restartcollection(g);
      g->gcstate = GCSpropagate;
      work = 1;
      break;
    }
    case GCSpropagate: {
      if (fast || g->gray == NULL) {
        g->gcstate = GCSenteratomic;  /* finish propagate phase */
        work = 0;
      }
      else {
        propagatemark(g);  /* traverse one gray object */
        work = 1;
      }
      break;
    }
    case GCSenteratomic: {
      work = atomic(L);
      if (checkmajorminor(L, g))
        entersweep(L);
      break;
    }
    case GCSswpallgc: {  /* sweep "regular" objects */
      sweepstep(L, g, GCSswpfinobj, &g->finobj, fast);
      work = GCSWEEPMAX;
      break;
    }
    case GCSswpfinobj: {  /* sweep objects with finalizers */
      sweepstep(L, g, GCSswptobefnz, &g->tobefnz, fast);
      work = GCSWEEPMAX;
      break;
    }
    case GCSswptobefnz: {  /* sweep objects to be finalized */
      sweepstep(L, g, GCSswpend, NULL, fast);
      work = GCSWEEPMAX;
      break;
    }
    case GCSswpend: {  /* finish sweeps */
      checkSizes(L, g);
      g->gcstate = GCScallfin;
      work = 0;
      break;
    }
    case GCScallfin: {  /* call finalizers */
      if (g->tobefnz && !g->gcemergency) {
        g->gcstopem = 0;  /* ok collections during finalizers */
        GCTM(L);  /* call one finalizer */
        work = 1;
      }
      else {  /* emergency mode or no more finalizers */
        g->gcstate = GCSpause;  /* finish collection */
        work = 0;
      }
      break;
    }
    default: lua_assert(0); return 0;
  }
  g->gcstopem = 0;
  return work;
}


// 步进GC收集器直到达到指定状态ss
/*
** Advances the garbage collector until it reaches the given state.
** (The option 'fast' is only for testing; in normal code, 'fast'
** here is always true.)
*/
void luaC_runtilstate (lua_State *L, int state, int fast) {
  global_State *g = G(L);
  lua_assert(g->gckind == KGC_INC);
  while (state != g->gcstate)
    singlestep(L, fast);
}



/*
** Performs a basic incremental step. The debt and step size are
** converted from bytes to "units of work"; then the function loops
** running single steps until adding that many units of work or
** finishing a cycle (pause state). Finally, it sets the debt that
** controls when next step will be performed.
*/
/*
增量模式单步收集
1）计算GC的速度(stepmul)和债务单元数量(debt)
2）计算单步需要收集的单元数量(stepsize)
3）执行单步收集，直到收集的内存达到stepsize或者状态达到PAUSE
4）如果状态为PAUSE，则完成一轮收集
5）否则重新计算债务
*/
static void incstep (lua_State *L, global_State *g) {
  l_obj stepsize = applygcparam(g, STEPSIZE, 100);
  l_obj work2do = applygcparam(g, STEPMUL, stepsize);
  int fast = 0;
  if (work2do == 0) {  /* special case: do a full collection */
    work2do = MAX_LOBJ;  /* do unlimited work */
    fast = 1;
  }
  do {  /* repeat until pause or enough work */
    l_obj work = singlestep(L, fast);  /* perform one single step */
    if (g->gckind == KGC_GENMINOR)  /* returned to minor collections? */
      return;  /* nothing else to be done here */
    work2do -= work;
  } while (work2do > 0 && g->gcstate != GCSpause);
  if (g->gcstate == GCSpause)
    setpause(g);  /* pause until next cycle */
  else
    luaE_setdebt(g, stepsize);
}

/*
** Performs a basic GC step if collector is running. (If collector is
** not running, set a reasonable debt to avoid it being called at
** every single check.)
*/
/*
执行一次基础的GC步骤
1）判断收集器是否在运行
2）根据GC模式进行一次单步GC
*/
void luaC_step (lua_State *L) {
  global_State *g = G(L);
  lua_assert(!g->gcemergency);
  if (!gcrunning(g))  /* not running? */
    luaE_setdebt(g, 2000);
  else {
    switch (g->gckind) {
      case KGC_INC: case KGC_GENMAJOR:
        incstep(L, g);
        break;
      case KGC_GENMINOR:
        youngcollection(L, g);
        setminordebt(g);
        break;
    }
  }
}


/*
** Perform a full collection in incremental mode.
** Before running the collection, check 'keepinvariant'; if it is true,
** there may be some objects marked as black, so the collector has
** to sweep all objects to turn them back to white (as white has not
** changed, nothing will be collected).
*/
/*
执行一次增量模式的全量GC
1）如果不在扫描状态，则执行扫描
2）先等待收集器恢复PAUSE
3）执行一次全量收集，等待状态变成FIN状态
2）等待收集器恢复PAUSE
*/
static void fullinc (lua_State *L, global_State *g) {
  if (keepinvariant(g))  /* black objects? */
    entersweep(L); /* sweep everything to turn them back to white */
  /* finish any pending sweep phase to start a new cycle */
  luaC_runtilstate(L, GCSpause, 1);
  luaC_runtilstate(L, GCScallfin, 1);  /* run up to finalizers */
  /* 'marked' must be correct after a full GC cycle */
  lua_assert(g->marked == gettotalobjs(g));
  luaC_runtilstate(L, GCSpause, 1);  /* finish collection */
  setpause(g);
}


/*
** Performs a full GC cycle; if 'isemergency', set a flag to avoid
** some operations which could change the interpreter state in some
** unexpected ways (running finalizers and shrinking some structures).
*/
/*
进行一次全量GC
1）设置是否紧急GC的标识
2）根据GC模式进行一次全量GC
3）清除紧急GC标识
*/
void luaC_fullgc (lua_State *L, int isemergency) {
  global_State *g = G(L);
  lua_assert(!g->gcemergency);
  g->gcemergency = isemergency;  /* set flag */
  switch (g->gckind) {
    case KGC_GENMINOR: fullgen(L, g); break;
    case KGC_INC: fullinc(L, g); break;
    case KGC_GENMAJOR:
      g->gckind = KGC_INC;
      fullinc(L, g);
      g->gckind = KGC_GENMAJOR;
      break;
  }
  g->gcemergency = 0;
}

/* }====================================================== */


