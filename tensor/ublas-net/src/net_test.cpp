// Tests for network class

#define BOOST_TEST_DYN_LINK
#define BOOST_TEST_MODULE ublas_net_test
#include <boost/test/unit_test.hpp>

#include <iostream>
#include <iomanip>
#include <boost/numeric/ublas/io.hpp>

#include "utils/matrix_utils.h"
#include "net.h"

using namespace std;

BOOST_AUTO_TEST_SUITE(network_evaluations)

BOOST_AUTO_TEST_CASE(multiple_evaluations_yield_the_same_result) {
  INetworkMetadataPtr nm = NewLogisticFunctionBasedNetworkMetadata();
  INetworkPtr n = NewNetwork({3, 2, 1}, nm);
  BOOST_CHECK(n->String().size() > 0);

  cout << "Test two evaluations..." << setprecision(2) << endl;

  float_vector args{0.1f, 0.95f, 0.0f};
  auto result1 = ToMatrix1xN(n->Evaluate(args));
  auto result2 = ToMatrix1xN(n->Evaluate(args));

  cout << "Evaluation: result1=" << result1 << ", result2=" << result2 << endl;

  BOOST_CHECK_EQUAL(result1.size2(), result2.size2());
  BOOST_CHECK_EQUAL(result1(0, 0), result2(0, 0));
}

BOOST_AUTO_TEST_CASE(learn_nand_operation) {
  vector<TrainingData> trainingSet{
    TrainingData({0, 0}, {1}),
    TrainingData({0, 1}, {1}),
    TrainingData({1, 0}, {1}),
    TrainingData({1, 1}, {0}),
  };

  INetworkPtr n = NewNetwork({2, 1}, NewLogisticFunctionBasedNetworkMetadata());
  n->SGD(trainingSet, 400, 4, 30.0f);

  for (auto t : trainingSet) {
    auto output = n->Evaluate(t.input);

    cout << setprecision(2) << "input=" << ToMatrixNx1(t.input) <<
      ", output=" << ToMatrixNx1(output) << endl;
  }

  /*
  final List<TrainingData> trainingSet = Arrays.asList(
          TrainingData.withInput(0, 0).withOutput(1),
          TrainingData.withInput(1, 0).withOutput(1),
          TrainingData.withInput(0, 1).withOutput(1),
          TrainingData.withInput(1, 1).withOutput(0)
      );
      final SimpleNeuralNetwork n = new SimpleNeuralNetwork(metadata, new int[]{2, 1});
      //n.stochasticGradientDescent(trainingSet, 1000, 4, 3.0f, false);
      n.stochasticGradientDescent(trainingSet, 400, 4, 30.0f, false);

      for (final TrainingData trainingData : trainingSet) {
        final float[] output = n.evaluate(trainingData.getInput());

        // now check, that real output difference is in sync with the outputs:
        final float[] expected = trainingData.getOutput();
        //assertEquals(expected[0], output[0], 0.1);

        System.out.println("input=" + floatsToString(trainingData.getInput()) + ", output=" + floatsToString(output));
      }
  */
}

BOOST_AUTO_TEST_SUITE_END()
