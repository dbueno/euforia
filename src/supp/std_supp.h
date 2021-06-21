// Copyright 2021 National Technology & Engineering Solutions of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS, the U.S. Government retains certain rights in this software. See LICENSE.txt for details.
//
// Author: Denis Bueno


#ifndef stdsupp_hpp__
#define stdsupp_hpp__

#include <algorithm>
#include <chrono>
#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <type_traits>
#include <boost/optional.hpp>

template<class C, class T, class A>
static bool starts_with(std::basic_string<C,T,A> const& haystack,
                        std::basic_string<C,T,A> const& needle) {
  return needle.length() <= haystack.length() &&
  std::equal(needle.begin(), needle.end(), haystack.begin());
}

template<class C, class T, class A>
static bool starts_with(std::basic_string<C,T,A> const& haystack,
                        const char *needle) {
  return starts_with(haystack, std::string(needle));
}

inline static bool ends_with(const std::string& a, const std::string& b) {
  if (b.size() > a.size()) return false;
  return std::equal(a.begin() + a.size() - b.size(), a.end(), b.begin());
}

//^----------------------------------------------------------------------------^
//

template <template<class,class,class...> class C, typename K, typename V, typename... Args>
V GetWithDefault(const C<K,V,Args...>& m, K const& key, const V & defval) {
  typename C<K,V,Args...>::const_iterator it = m.find(key);
  if (it == m.end())
    return defval;
  return it->second;
}

template <template<class,class,class...> class C, typename K, typename V, typename... Args>
V& GetOrInsert(const C<K,V,Args...>& m, K const& key, const V & defval) {
  if (m.find(key) == m.end()) {
    m.insert({key, defval});
  }
  return m.at(key);
}

//^----------------------------------------------------------------------------^
//

template <class DelimT, class CharT = char,
          class Traits = std::char_traits<CharT>>
class ostream_joiner {
 public:
  using char_type = CharT;
  using traits_type = Traits;
  using ostream_type = std::basic_ostream<CharT, Traits>;
  using value_type = void;
  using difference_type = void;
  using pointer = void;
  using reference = void;
  using iterator_category = std::output_iterator_tag;

  ostream_joiner(std::ostream& os, const DelimT& delimeter)
      : os_(os), delimeter_(delimeter), first_(true) {}

  template <class T>
  ostream_joiner& operator=(const T& value) {
    if (!first_) {
      os_ << delimeter_;
    }
    first_ = false;
    os_ << value;
    return *this;
  }

  ostream_joiner& operator*() { return *this; }
  ostream_joiner& operator++() { return *this; }
  ostream_joiner& operator++(int) { return *this; }

 private:
  std::ostream& os_;
  DelimT delimeter_;
  bool first_;
};

template <class charT, class traits, class DelimT>
ostream_joiner<std::decay_t<DelimT>, charT, traits>
make_ostream_joiner(std::basic_ostream<charT, traits>& os, DelimT&& delimeter) {
  return ostream_joiner<std::decay_t<DelimT>, charT, traits>(
      os, std::forward<DelimT>(delimeter));
}

//^----------------------------------------------------------------------------^
//

template <class T>
void *addressof_void(T& arg) {
  return static_cast<void*>(std::addressof(arg));
}

#define RETURNS(...) -> decltype(__VA_ARGS__) { return (__VA_ARGS__); }

// https://stackoverflow.com/questions/12672372/boost-transform-iterator-and-c11-lambda
// Makes a default-constructible function object from a lambda.
template<class Fun>
struct function_object
{
  boost::optional<Fun> f;

  function_object() {}
  function_object(Fun f): f(f) {}

  function_object(const function_object & rhs) : f(rhs.f) {}

  // Assignment operator is just a copy construction, which does not provide
  // the strong exception guarantee.
  function_object& operator=(const function_object& rhs) {
    if (this != &rhs)
    {
      this->~function_object();
      new (this) function_object(rhs);
    }
    return *this;
  }

  template<class F>
  struct result
  {};

  template<class F, class T>
  struct result<F(T)>
  {
    typedef decltype(std::declval<Fun>()(std::declval<T>())) type;
  };

  template<class T>
      auto operator()(T && x) const RETURNS((*f)(std::forward<T>(x)))

      template<class T>
      auto operator()(T && x) RETURNS((*f)(std::forward<T>(x)))
};

template<class F>
function_object<F> make_function_object(F f)
{
  return function_object<F>(f);
}


//^----------------------------------------------------------------------------^
//

namespace euforia {

// Exponential moving average over last N items
template <typename Rep = double>
class ExpAvgT {

 private:
  Rep avg_ = 0.0;

 public:
  const Rep alpha_; // 2/(N+1) where I assume N is the number of queries I'm wanting to be most "important" in the avg

  ExpAvgT(unsigned N) : alpha_(2.f/(static_cast<Rep>(N)+static_cast<Rep>(1.0))) {}

  inline Rep get() const { return avg_; }

  template <typename Num>
  inline Rep percent(Num total) const {
    // Don't divide by 0
    if (static_cast<Rep>(total) == 0.0) {
      return static_cast<Rep>(0.0);
    }
    return (get() / static_cast<Rep>(total)) * static_cast<Rep>(100.);
  }

  template <typename Num>
  inline ExpAvgT& operator+=(Num c) {
    avg_ = (static_cast<Rep>(c)-avg_) * alpha_ + avg_;
    return *this;
  }

  template <typename Num>
  inline ExpAvgT operator+(Num c) const {
    ExpAvgT a(*this);
    a += c;
    return a;
  }
};

using ExpAvg = ExpAvgT<double>;

template <typename Rep = double, typename NRep = int64_t>
class RunningAvgT {
  Rep avg_;
  NRep n_;

 public:
  RunningAvgT() : avg_(static_cast<Rep>(0)), n_(static_cast<NRep>(0)) {}

  inline Rep get() const { return avg_; }

  template <typename Num>
  inline RunningAvgT& operator+=(Num c) {
    avg_ = (c + n_*avg_) / (n_+1);
    ++n_;
    return *this;
  }

  template <typename Num>
  inline RunningAvgT operator+(Num c) const {
    ExpAvgT<Rep> a(*this);
    a += c;
    return a;
  }
};

using RunningAvg = RunningAvgT<double, int64_t>;

template <typename Rep>
class RunningMaxT {
  Rep max_;

 public:
  RunningMaxT(Rep init) : max_(init) {}

  inline Rep get() const { return max_; }

  template <typename Num>
  inline RunningMaxT& operator+=(Num c) {
    max_ = std::max(max_, c);
    return *this;
  }
};

using RunningMax = RunningMaxT<int64_t>;

}

#endif
