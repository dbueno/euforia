#ifndef EUFORIA_SHARED_CONTAINER_ITERATOR_H_
#define EUFORIA_SHARED_CONTAINER_ITERATOR_H_

#include <boost/iterator/iterator_adaptor.hpp>
#include <boost/range/iterator_range.hpp>

template <class Container>
class shared_container_iterator
    : public boost::iterator_adaptor<shared_container_iterator<Container>,
                                     typename Container::iterator> {
 public:
  shared_container_iterator() = default;
  shared_container_iterator(typename Container::iterator x,
                            std::shared_ptr<Container> c)
      : shared_container_iterator::iterator_adaptor(x), ref_(std::move(c)) {}
 private:
  std::shared_ptr<Container> ref_;
};

template<class Container>
auto make_shared_container_range(std::shared_ptr<Container> const& container) {
    return boost::make_iterator_range(
        shared_container_iterator{container->begin(), container},
        shared_container_iterator{container->end(), container});
}

#endif
