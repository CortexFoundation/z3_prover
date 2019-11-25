#ifndef Z3_CVM_BASE_H
#define Z3_CVM_BASE_H

#include <exception>
#include <sstream>

#if defined(__GNUC__)
#define Z3UTIL_ATTRIBUTE_UNUSED __attribute__((unused))
#else
#define Z3UTIL_ATTRIBUTE_UNUSED
#endif

#define Z3UTIL_STR_CONCAT_(__x, __y) __x##__y
#define Z3UTIL_STR_CONCAT(__x, __y) Z3UTIL_STR_CONCAT_(__x, __y)

#define VERIFY(__x) \
  if (!(__x)) \
    RuntimeError(__FILE__, __LINE__).Stream() \
      << "Verify Failed: " #__x << "\n"

#define THROW() VERIFY(false)
#define VERIFY_EQ(__x, __y) VERIFY(__x == __y)
#define VERIFY_NE(__x, __y) VERIFY(__x != __y)

class RuntimeError {
 public:
  RuntimeError(const char *file, int line) {
    oss << "\n\nFILE [" << file  << "] "
      << "LINE:" << line << "\n";
  }

  inline std::ostream& Stream() { return oss; }

  ~RuntimeError() noexcept(false) {
    oss << "\n\n";
    throw std::runtime_error(oss.str());
  }

 private:
  std::ostringstream oss;

};

/*
 * Simplify Level indicates the z3 prover's condition simplicity.
 *  Lower number is easy for debug with user-friendly constraints printer;
 *  Higher number is efficiently speed up the prove time cost;
 *
 *  The range of SIMPLIFY_LEVEL is between [0, 10] and default
 *    value is 5, [0, 4] is easy to read with frequently func-declare
 *    of base operator such as safe_div (which is wrapper function for
 *    processing zero-division), and [6, 10] is to do cond-reduction
 *    as most as we can for less time provement.
 **/
#define SIMPLIFY_LEVEL 5

#endif // Z3_CVM_BASE_H
