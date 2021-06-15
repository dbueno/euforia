// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef EUFORIA_POOL_STORAGE_H_
#define EUFORIA_POOL_STORAGE_H_

#include <unordered_map>
#include <memory>

namespace euforia {
namespace util {

//! Pool that manages unique ptrs. Never allocates objects with the same key
//! twice. Objects stick around until the pool is deallocated.
template <class T,
          class KeyType = std::size_t,
          class MakeKey = std::hash<T>>
class pool_storage_std {
 private:
  using StoredPtr = std::unique_ptr<T>;

 public:
  template <class ... Args>
  inline T& operator()(Args&& ... args) {
    KeyType key = MakeKey()(args...);
    if (auto it = instances_.find(key); it != instances_.end()) {
      if (T* existing = it->second.get()) {
        return *existing;
      } else {
        instances_.erase(key);
      }
    }
    StoredPtr new_instance = std::make_unique<T>(args...);
    auto *ret = new_instance.get();
    instances_.emplace(key, std::move(new_instance));
    return *ret;
  }

 private:
  std::unordered_map<KeyType, StoredPtr, std::hash<KeyType>,
      std::equal_to<KeyType>>
  instances_;

};

} // end namespace util
} // end namespace euforia

#endif // EUFORIA_POOL_STORAGE_H_
