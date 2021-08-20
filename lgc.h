/*
** $Id: lgc.h $
** Garbage Collector
** See Copyright Notice in lua.h
*/

#ifndef lgc_h
#define lgc_h


#include "lobject.h"
#include "lstate.h"

/*
** Collectable objects may have one of three colors: white, which means
** the object is not marked; gray, which means the object is marked, but
** its references may be not marked; and black, which means that the
** object and all its references are marked.  The main invariant of the
** garbage collector, while marking objects, is that a black object can
** never point to a white one. Moreover, any gray object must be in a
** "gray list" (gray, grayagain, weak, allweak, ephemeron) so that it
** can be visited again before finishing the collection cycle. (Open
** upvalues are an exception to this rule.)  These lists have no meaning
** when the invariant is not being enforced (e.g., sweep phase).
*/


/*
** Possible states of the Garbage Collector
*/
#define GCSpropagate	0
#define GCSenteratomic	1
#define GCSatomic	2
#define GCSswpallgc	3
#define GCSswpfinobj	4
#define GCSswptobefnz	5
#define GCSswpend	6
#define GCScallfin	7
#define GCSpause	8


#define issweepphase(g)  \
	(GCSswpallgc <= (g)->gcstate && (g)->gcstate <= GCSswpend)


/*
** macro to tell when main invariant (white objects cannot point to black
** ones) must be kept. During a collection, the sweep
** phase may break the invariant, as objects turned white may point to
** still-black objects. The invariant is restored when sweep ends and
** all objects are white again.
*/

/*
检查在什么GC状态主不变量是稳定的（白色对象不能指向黑色对象）
在扫描过程中，可能会破坏稳定状态
*/
#define keepinvariant(g)	((g)->gcstate <= GCSatomic)


/*
** some useful bit tricks
*/
#define resetbits(x,m)		((x) &= cast_byte(~(m)))
#define setbits(x,m)		((x) |= (m))
#define testbits(x,m)		((x) & (m))
#define bitmask(b)		(1<<(b))
#define bit2mask(b1,b2)		(bitmask(b1) | bitmask(b2))
#define l_setbit(x,b)		setbits(x, bitmask(b))
#define resetbit(x,b)		resetbits(x, bitmask(b))
#define testbit(x,b)		testbits(x, bitmask(b))


/*
** Layout for bit use in 'marked' field. First three bits are
** used for object "age" in generational mode. Last bit is used
** by tests.
*/
/* 前3bit（0-7）用来存储age */
#define WHITE0BIT	3  /* object is white (type 0) */
#define WHITE1BIT	4  /* object is white (type 1) */
#define BLACKBIT	5  /* object is black */
#define FINALIZEDBIT	6  /* object has been marked for finalization */

#define TESTBIT		7



#define WHITEBITS	bit2mask(WHITE0BIT, WHITE1BIT)


/*
1）iswhite: 判断x是white
2）isblack: 判断x是black
3）isgray: 判断x是gray（black + white）
4）tofinalize: 判断x是finalize
*/
#define iswhite(x)      testbits((x)->marked, WHITEBITS)
#define isblack(x)      testbit((x)->marked, BLACKBIT)
#define isgray(x)  /* neither white nor black */  \
	(!testbits((x)->marked, WHITEBITS | bitmask(BLACKBIT)))

#define tofinalize(x)	testbit((x)->marked, FINALIZEDBIT)

/*
1）otherwhite: 翻转currentwhite的white bit(3/4)
2）isdeadm: 与otherwhite相同，与currentwhite相反，上一轮的对象，需要被释放
3）isdead: 判断对象v是否死亡
4）changewhite: 清除掉white bit
5）nw2black: mark添加black bit
6）luaC_white: 返回currentwhite
*/
#define otherwhite(g)	((g)->currentwhite ^ WHITEBITS)
#define isdeadm(ow,m)	((m) & (ow))
#define isdead(g,v)	isdeadm(otherwhite(g), (v)->marked)

#define changewhite(x)	((x)->marked ^= WHITEBITS)
#define nw2black(x)  \
	check_exp(!iswhite(x), l_setbit((x)->marked, BLACKBIT))

#define luaC_white(g)	cast_byte((g)->currentwhite & WHITEBITS)


/* object age in generational mode */
#define G_NEW		0	/* created in current cycle */
#define G_SURVIVAL	1	/* created in previous cycle */
#define G_OLD0		2	/* marked old by frw. barrier in this cycle */
#define G_OLD1		3	/* first full cycle as old */
#define G_OLD		4	/* really old object (not to be visited) */
#define G_TOUCHED1	5	/* old object touched this cycle */
#define G_TOUCHED2	6	/* old object touched in previous cycle */

#define AGEBITS		7  /* all age bits (111) */

/*
1）getage: 返回对象o的age
2）setage: 设置对象o的age
3）isold: 对象o的age大于存活都是OLD
4）changeage: 改变对象o的age
*/
#define getage(o)	((o)->marked & AGEBITS)
#define setage(o,a)  ((o)->marked = cast_byte(((o)->marked & (~AGEBITS)) | a))
#define isold(o)	(getage(o) > G_SURVIVAL)

#define changeage(o,f,t)  \
	check_exp(getage(o) == (f), (o)->marked ^= ((f)^(t)))


/* Default Values for GC parameters */
#define LUAI_GENMAJORMUL         100
#define LUAI_GENMINORMUL         20

/* wait memory to double before starting new cycle */
#define LUAI_GCPAUSE    200

/*
** some gc parameters are stored divided by 4 to allow a maximum value
** up to 1023 in a 'lu_byte'.
*/
/*
gc参数转换，允许某些参数达到1023，但能存储到一个byte内
*/
#define getgcparam(p)	((p) * 4)
#define setgcparam(p,v)	((p) = (v) / 4)

#define LUAI_GCMUL      100

/* how much to allocate before next GC step (log2) */
/* lua单步gc收集的字节数 */
#define LUAI_GCSTEPSIZE 13      /* 8 KB */


/*
** Check whether the declared GC mode is generational. While in
** generational mode, the collector can go temporarily to incremental
** mode to improve performance. This is signaled by 'g->lastatomic != 0'.
*/
/*
是否声明了分代GC模式
分代GC模式可以临时转换到增量模式以提升性能，因此lastatomic不等于0也表示分代
*/
#define isdecGCmodegen(g)	(g->gckind == KGC_GEN || g->lastatomic != 0)

/*
** Does one step of collection when debt becomes positive. 'pre'/'pos'
** allows some adjustments to be done only when needed. macro
** 'condchangemem' is used only for heavy tests (forcing a full
** GC cycle on every opportunity)
*/
/*
检查是否可以进行GC
1）GCdebt必须大于0
2）此函数由内部触发
*/
#define luaC_condGC(L,pre,pos) \
	{ if (G(L)->GCdebt > 0) { pre; luaC_step(L); pos;}; \
	  condchangemem(L,pre,pos); }

/* more often than not, 'pre'/'pos' are empty */
/* 检查是否可以进行GC */
#define luaC_checkGC(L)		luaC_condGC(L,(void)0,(void)0)


#define luaC_barrier(L,p,v) (  \
	(iscollectable(v) && isblack(p) && iswhite(gcvalue(v))) ?  \
	luaC_barrier_(L,obj2gco(p),gcvalue(v)) : cast_void(0))

#define luaC_barrierback(L,p,v) (  \
	(iscollectable(v) && isblack(p) && iswhite(gcvalue(v))) ? \
	luaC_barrierback_(L,p) : cast_void(0))

#define luaC_objbarrier(L,p,o) (  \
	(isblack(p) && iswhite(o)) ? \
	luaC_barrier_(L,obj2gco(p),obj2gco(o)) : cast_void(0))

LUAI_FUNC void luaC_fix (lua_State *L, GCObject *o);
LUAI_FUNC void luaC_freeallobjects (lua_State *L);
LUAI_FUNC void luaC_step (lua_State *L);
LUAI_FUNC void luaC_runtilstate (lua_State *L, int statesmask);
LUAI_FUNC void luaC_fullgc (lua_State *L, int isemergency);
LUAI_FUNC GCObject *luaC_newobj (lua_State *L, int tt, size_t sz);
LUAI_FUNC void luaC_barrier_ (lua_State *L, GCObject *o, GCObject *v);
LUAI_FUNC void luaC_barrierback_ (lua_State *L, GCObject *o);
LUAI_FUNC void luaC_checkfinalizer (lua_State *L, GCObject *o, Table *mt);
LUAI_FUNC void luaC_changemode (lua_State *L, int newmode);


#endif
