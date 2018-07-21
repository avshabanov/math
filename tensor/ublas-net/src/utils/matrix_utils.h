// This file defines header-only matrix utils
#pragma once

#include <boost/numeric/ublas/matrix.hpp>
#include <vector>

// ToMatrixNx1 converts given vector to Nx1 2D matrix, that is a [1, 2] vector becomes [[1], [2]] matrix
template<class TElement>
static inline boost::numeric::ublas::matrix<TElement> ToMatrixNx1(const std::vector<TElement>& v) {
  boost::numeric::ublas::matrix<TElement> m(v.size(), 1);
  for (auto i = 0; i < v.size(); ++i) {
    m(i, 0) = v[i];
  }
  return m;
}

// ToMatrix1xN converts given vector to 1xN 2D matrix, that is a [1, 2] vector becomes [[1, 2]] matrix
template<class TElement>
static inline boost::numeric::ublas::matrix<TElement> ToMatrix1xN(const std::vector<TElement>& v) {
  boost::numeric::ublas::matrix<TElement> m(1, v.size());
  for (auto i = 0; i < v.size(); ++i) {
    m(0, i) = v[i];
  }
  return m;
}
