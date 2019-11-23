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

#endif // Z3_CVM_BASE_H
