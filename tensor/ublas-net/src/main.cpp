#include "net.h"
#include "utils/matrix_utils.h"

#include <iostream>
#include <iomanip>

#include <boost/numeric/ublas/io.hpp>

using namespace std;

static void evaluateSimpleNetwork() {
  auto nm = NewLogisticFunctionBasedNetworkMetadata();
  auto n = NewNetwork({3, 2, 1}, nm);
  
  cout << setprecision(2); // prepare to display floats
  cout << "Network: " << n->String() << endl;

  float_vector args{0.1f, 0.95f, 0.0f};
  auto result = n->Evaluate(args);
  cout << "Evaluation result: " << ToMatrix1xN(result) << endl << "---" << endl;
  
  auto result2 = n->Evaluate(args);
  cout << "2nd evaluation, result2=" << ToMatrix1xN(result2) << endl;
}

// Entry point
int main(int argc, char** argv) {
  evaluateSimpleNetwork();
  return 0;
}

