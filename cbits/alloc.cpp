#ifdef _WIN32
#include <cstdlib>
#include <cstdint>
#else
#include "./parlaylib/include/parlay/alloc.h"
#endif

extern "C" {

  void* accelerate_raw_alloc(uint64_t size, uint64_t align) {
#ifdef _WIN32
    return _aligned_malloc(size, align);
#else
    return parlay::p_malloc(size, align);
#endif
  }

  void accelerate_raw_free(void *ptr) {
#ifdef _WIN32
    _aligned_free(ptr);
#else
    parlay::p_free(ptr);
#endif
  }

}
