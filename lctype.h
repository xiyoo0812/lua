/*
** $Id: lctype.h $
** 'ctype' functions for Lua
** See Copyright Notice in lua.h
*/

#ifndef lctype_h
#define lctype_h

#include "lua.h"


/*
** WARNING: the functions defined here do not necessarily correspond
** to the similar functions in the standard C ctype.h. They are
** optimized for the specific needs of Lua.
*/

#if !defined(LUA_USE_CTYPE)

#if 'A' == 65 && '0' == 48
/* ASCII case: can use its own tables; faster and fixed */
#define LUA_USE_CTYPE	0
#else
/* must use standard C ctype */
#define LUA_USE_CTYPE	1
#endif

#endif


#if !LUA_USE_CTYPE	/* { */

#include <limits.h>

#include "llimits.h"


#define ALPHABIT	0
#define DIGITBIT	1
#define PRINTBIT	2
#define SPACEBIT	3
#define XDIGITBIT	4


#define MASK(B)		(1 << (B))

//本文件用于lua代码词法分析，解析代码字符，可以使用ctype，也可以使用自定义接口。

/*
** add 1 to char to allow index -1 (EOZ)
*/
#define testprop(c,p)	(luai_ctype_[(c)+1] & (p))

/*
** 'lalpha' (Lua alphabetic) and 'lalnum' (Lua alphanumeric) both include '_'
*/

/*
- 表中的二进制值
- 0x04       对应的二进制为   00000100  
- 0x16       对应的二进制为   00010110
- 0x15       对应的二进制为   00010101
- 0x05       对应的二进制为   00000101
- 0x08       对应的二进制为   00001000
- 0x0c       对应的二进制为   00001100
- 0x00       对应的二进制为   00000000
*/

/*
    MASK(ALPHABIT) == 1，testprop中p为1，若要结果为真，
    则传入的c在luai_ctype_表中对应值二进制末尾是1，符合条件的有0x05, 0x15
    对于的index(c+1)刚好是66-91，98-123，那么c自然和ascii码对应上了
*/
#define lislalpha(c)	testprop(c, MASK(ALPHABIT))
/*
    MASK(ALPHABIT) == 1，MASK(DIGITBIT) == 2，testprop中p为3，若要结果为真，
    则传入的c在luai_ctype_表中对应值二进制末2尾是必须有1，符合条件的有0x05, 0x15，0x16
    对于的index(c+1)刚好是49-58,66-91，98-123，那么c自然和ascii码对应上了
*/
#define lislalnum(c)	testprop(c, (MASK(ALPHABIT) | MASK(DIGITBIT)))
#define lisdigit(c)	testprop(c, MASK(DIGITBIT))
#define lisspace(c)	testprop(c, MASK(SPACEBIT))
#define lisprint(c)	testprop(c, MASK(PRINTBIT))
#define lisxdigit(c)	testprop(c, MASK(XDIGITBIT))


/*
** In ASCII, this 'ltolower' is correct for alphabetic characters and
** for '.'. That is enough for Lua needs. ('check_exp' ensures that
** the character either is an upper-case letter or is unchanged by
** the transformation, which holds for lower-case letters and '.'.)
*/
#define ltolower(c)  \
  check_exp(('A' <= (c) && (c) <= 'Z') || (c) == ((c) | ('A' ^ 'a')),  \
            (c) | ('A' ^ 'a'))


/* one entry for each character and for -1 (EOZ) */
LUAI_DDEC(const lu_byte luai_ctype_[UCHAR_MAX + 2];)


#else			/* }{ */

/*
** use standard C ctypes
*/

#include <ctype.h>


#define lislalpha(c)	(isalpha(c) || (c) == '_')
#define lislalnum(c)	(isalnum(c) || (c) == '_')
#define lisdigit(c)	(isdigit(c))
#define lisspace(c)	(isspace(c))
#define lisprint(c)	(isprint(c))
#define lisxdigit(c)	(isxdigit(c))

#define ltolower(c)	(tolower(c))

#endif			/* } */

#endif

