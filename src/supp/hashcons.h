// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno

#ifndef hashcons_hpp
#define hashcons_hpp


#include <unordered_map>
#include <memory>


//! A class that holds pointers to objects that specialize std::hash, or
//! whatever you want by assigning MakeKey.
//!
//! A hashcons has two properties:
//! 1. Never makes two distinct objects in memory that have the same key.
//! 2. When there are no longer any external references to an object, it is
//!    deallocated.
template <class T,
          class KeyType = std::size_t,
          class MakeKey = std::hash<T>>
class hashcons_std {
 public:
  template <class ... Args>
  inline std::shared_ptr<T> operator()(Args&& ... args) {
    KeyType key = MakeKey()(args...);
    if (auto it = instances_.find(key); it != instances_.end()) {
      if (std::shared_ptr<T> existing = it->second.lock()) {
        return existing;
      } else {
        instances_.erase(key);
      }
    }
    std::shared_ptr<T> new_instance(new T(args...), [this,key] (T *x) {
                                    instances_.erase(key);
                                    delete x;
                                    });
    instances_.insert({key, new_instance});
    return new_instance;
  }

 private:
  std::unordered_map<KeyType, std::weak_ptr<T>, std::hash<KeyType>,
      std::equal_to<KeyType>> instances_;

};




#endif /* hashcons_hpp */
