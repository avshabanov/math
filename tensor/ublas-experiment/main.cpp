#include <cstdio>
#include <vector>

#include <boost/numeric/ublas/matrix.hpp>
#include <boost/numeric/ublas/io.hpp>

namespace ub = boost::numeric::ublas;

typedef std::vector<float> fvec;

static ub::matrix<float> matrix2x2(size_t size1, size_t size2, const fvec& elements) {
  ub::matrix<float> m(size1, size2);
  // TODO: assert sizes
  std::copy(elements.begin(), elements.end(), m.data().begin());
  return m;
}

static void elementwise_transform() {
  std::cout << "in elementwise_transform():" << std::endl;

  auto m = matrix2x2(2, 3, {1, 2, 3, 4, 5, 6});
  std::cout << "\toriginal m=" << m << std::endl;

  // [](double d) -> double { return d * 3; }
  std::transform(m.data().begin(), m.data().end(), m.data().begin(),
      [](float d) { return d * 2.0f; });
  std::cout << "\ttransformed m=" << m << std::endl;
}

// Entry point
int main(int argc, char** argv) {
  ub::matrix<double> m(3, 3);
  for (auto i = 0; i < m.size1(); ++ i) {
    for (auto j = 0; j < m.size2(); ++ j) {
      m(i, j) = 3 * i + j;
    }
  }
  std::cout << m << std::endl;

  elementwise_transform();
  return 0;
}

