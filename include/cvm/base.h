#ifndef Z3_CVM_BASE_H
#define Z3_CVM_BASE_H

#if defined(__GNUC__)
#define Z3UTIL_ATTRIBUTE_UNUSED __attribute__((unused))
#else
#define Z3UTIL_ATTRIBUTE_UNUSED
#endif

#define Z3UTIL_STR_CONCAT_(__x, __y) __x##__y
#define Z3UTIL_STR_CONCAT(__x, __y) Z3UTIL_STR_CONCAT_(__x, __y)

#endif // Z3_CVM_BASE_H
