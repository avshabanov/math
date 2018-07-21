#include "net.h"
#include "utils/matrix_utils.h"

#include <iostream>
#include <iomanip>
#include <string>
#include <stdexcept>
#include <algorithm>
#include <random>
#include <chrono>

#include <boost/numeric/ublas/io.hpp>
#include <boost/numeric/ublas/matrix.hpp>
#include <boost/numeric/ublas/operation.hpp>

namespace ub = boost::numeric::ublas;
typedef ub::matrix<float> float_matrix;

using namespace std;

class Segment {
private:
  float_matrix mWeights;
  float_matrix mBiases;

public:
  Segment(int previousLayerSize, int layerSize, INetworkMetadataPtr metadata) :
    mWeights(layerSize, previousLayerSize),
    mBiases(layerSize, 1) {
    metadata->RandFill(mWeights.data());
    metadata->RandFill(mBiases.data());
  }

  Segment(const Segment& prototype, bool copyData) :
    mWeights(prototype.mWeights.size1(), prototype.mWeights.size2()),
    mBiases(prototype.mBiases.size1(), 1) {
    if (copyData) {
      copy(prototype.mWeights.data().begin(), prototype.mWeights.data().end(), mWeights.data().begin());
      copy(prototype.mBiases.data().begin(), prototype.mBiases.data().end(), mBiases.data().begin());
    }
  }

  Segment(const float_matrix& weights, const float_matrix& biases) : mWeights(weights), mBiases(biases) {
    if (weights.size1() != biases.size1()) {
      throw new logic_error("weights/biases size1 mismatch");
    }
  }

  string String() const {
    ostringstream ss;
    ss << "Layer#{" << setprecision(2) << "weights=" << mWeights;
    ss << ", biases=" << mBiases;
    ss << '}';
    return ss.str();
  }

  template<class SigmoidFunction>
  float_matrix Feedforward(
    const float_matrix& prevActivations,
    SigmoidFunction calcSigmoid,
    float_matrix* outZValues
  ) const {
    auto values = mBiases;
    values += ub::prod(mWeights, prevActivations); // values = z = b + w * a
    
    // save z-values for future reference
    if (outZValues != nullptr) {
      *outZValues = values;
    }

    calcSigmoid(values.data()); // values = s(z)

    return values;
  }

  // CalcWeightsDelta calculates Transpose(W)*Delta
  float_matrix CalcWeightsDelta(const float_matrix& delta) const {
    // TODO: use optimized way to calculate transposed matrix multiplication: r = w^T * d
    return ub::prod(ub::trans(mWeights), delta);
  }

  void Mul(float factor) {
    for (auto it = mBiases.data().begin(); it != mBiases.data().end(); ++it) {
      *it = factor * (*it);
    }

    for (auto it = mWeights.data().begin(); it != mWeights.data().end(); ++it) {
      *it = factor * (*it);
    }
  }

  void Add(const Segment& segment) {
    mBiases += segment.mBiases;
    mWeights += segment.mWeights;
  }

  void Sub(const Segment& segment) {
    mBiases -= segment.mBiases;
    mWeights -= segment.mWeights;
  }
};

// SegmentPtr defines a smart pointer to the segment
typedef shared_ptr<Segment> SegmentPtr;

// Network defines neural network interface
class Network : public INetwork {
  vector<SegmentPtr> mSegments;
  INetworkMetadataPtr mMetadata;

public:
  Network(const vector<int> layerSizes, INetworkMetadataPtr metadata) : mMetadata(metadata) {
    auto segmentCount = layerSizes.size() - 1;
    mSegments.reserve(segmentCount);

    for (auto i = 0; i < segmentCount; ++i) {
      SegmentPtr sp(new Segment(layerSizes[i], layerSizes[i + 1], metadata));
      mSegments.push_back(sp);
    }
  }

  virtual ~Network() {
#ifdef UBLASNET_DEBUG
    cout << "Disposing network" << endl;
#endif
  }

  virtual std::string String() {
    ostringstream ss;
    ss << '[';
    for (auto it = mSegments.begin(); it != mSegments.end(); ++it) {
      ss << (it != mSegments.begin() ? ", " : "") << (*it)->String();
    }
    ss << ']';
    return ss.str();
  }

  virtual float_vector Evaluate(const float_vector& input) {
    auto t = ToMatrixNx1(input);

    for (auto it = mSegments.begin(); it != mSegments.end(); ++it) {
#ifdef UBLASNET_DEBUG
      cout << "[DBG] Feedforward: " << (*it)->String() << ", t=" << t << endl;
#endif
      t = feedforward(*it, t);
    }

    float_vector result(t.data().size());
    copy(t.data().begin(), t.data().end(), result.begin());
#ifdef UBLASNET_DEBUG
    cout << "[DBG] Evaluate=" << setprecision(2) << t << endl << "---" << endl;
#endif
    return result;
  }

  size_t LayerCount() const {
    return mSegments.size() + 1;
  }

  void SGD(
    const vector<TrainingData>& trainingSet,
    size_t epochs,
    size_t miniBatchSize,
    float eta,
    bool reportEpoch = false
  ) {
    vector<TrainingData> mutableTrainingSet(trainingSet);
    auto trainingSetSize = mutableTrainingSet.size();
    auto batchCount = trainingSetSize / miniBatchSize;
    auto rng = default_random_engine{};

    for (auto j = 0; j < epochs; ++j) {
      auto epochStartTime = chrono::high_resolution_clock::now();

      shuffle(mutableTrainingSet.begin(), mutableTrainingSet.end(), rng);

      for (auto k = 0; k < batchCount; ++k) {
        auto startIndex = k * miniBatchSize;
        updateMiniBatch(vector<TrainingData>(&mutableTrainingSet[startIndex],
          &mutableTrainingSet[startIndex + min(startIndex + miniBatchSize, trainingSetSize)]), eta);
      }

      if (reportEpoch) {
        auto epochEndTime = chrono::high_resolution_clock::now();
        auto duration = chrono::duration_cast<chrono::milliseconds>(epochEndTime - epochStartTime).count();
        cout << "Epoch " << j << " took " << duration << "ms to complete";
      }
    }
  }

private:

  float_matrix feedforward(SegmentPtr s, const float_matrix& values, float_matrix* zValues = nullptr) const {
    auto calcSigmoid = [this](float_array& x) { mMetadata->CalcSigmoid(x); };
    return s->Feedforward(values, calcSigmoid, zValues);
  }

  //
  // Learning
  //

  // costDerivative calculates derivative of the cost function by using given actual (or activations) and
  // expected (or training output) matrices
  static float_matrix costDerivative(const float_matrix& actual, const float_matrix& expected) {
    return actual - expected;
  }

  vector<SegmentPtr> backprop(const float_vector& x, const float_vector& y) const {
    auto activation = ToMatrixNx1(x);
    auto expected_output = ToMatrixNx1(y);

    vector<float_matrix> activations(LayerCount());
    activations[0] = activation;

    // Collect computed Z' (z-prime values) across all layers
    vector<float_matrix> zPrimeValueSet(mSegments.size());

    // compute all activations and store intermediate z-vectors
    for (auto i = 0; i < mSegments.size(); ++i) {
      float_matrix zValues;
      activation = feedforward(mSegments[i], activation, &zValues);
      activations[i + 1] = activation;

      // zValues transform to zPrimes
      mMetadata->CalcSigmoidPrime(zValues.data());
      zPrimeValueSet.push_back(zValues);
    }

    vector<SegmentPtr> nablas(mSegments.size());

    float_matrix delta;
    auto lastSegmentIndex = mSegments.size() - 1;
    SegmentPtr seg = nullptr;
    for (auto i = 0; i < mSegments.size(); ++i) {
      auto zPrimes = zPrimeValueSet[zPrimeValueSet.size() - i - 1];

      if (i == 0) {
        // last layer: infer delta using cost derivative function
        delta = costDerivative(activations[activations.size() - 1], expected_output);
      } else {
        delta = seg->CalcWeightsDelta(delta);
      }

      seg = mSegments[lastSegmentIndex - i];
      
      // here: finalize computing delta as C'(An, Y) . S'(Zn), where An is last activation layer values and
      // Zn - is last activation layer's z-values and .-operation designates Hadamard Product
      // Delta(L-1) = Transpose(W(L-1)) * Delta(L) * S'(Z(L-1))
      for (auto i = 0; i < delta.size1(); ++i) {
        delta(i, 0) = delta(i, 0) * zPrimes(i, 0); 
      }

      // TODO: calculate a^T * delta in an optimized fashion (AXPY-product)
      auto transposedActivations = ub::trans(activations[activations.size() - i - 2]);
      //cout << setprecision(2) << "[DBG] backprop: a^T=" << transposedActivations << ", delta=" << delta << endl;

      auto weights = ub::prod(delta, transposedActivations);
      nablas[lastSegmentIndex - i] = SegmentPtr(new Segment(weights, delta /*biases*/));
    }

    return nablas;
  }

  vector<SegmentPtr> calculateNablas(const vector<TrainingData>& miniBatch) const {
    auto segmentCount = mSegments.size();
    vector<SegmentPtr> nablas(segmentCount); // don't use reserve to get indexing error if something goes wrong
    for (auto i = 0; i < segmentCount; ++i) {
      nablas[i] = SegmentPtr(new Segment(*mSegments[i], true/*copy*/));
    }

    for (auto trainingData : miniBatch) {
      // invoke backpropagation algorithm to populate 'delta nablas' that will be collected in the actual nabla
      // which is then will be used to adjust weights and biases in the network
      auto deltaNablas = this->backprop(trainingData.input, trainingData.output);
      for (auto i = 0; i < segmentCount; ++i) {
        nablas[i]->Add(*deltaNablas[i]);
      }
    }

    return nablas;
  }

  void updateMiniBatch(const vector<TrainingData>& miniBatch, float eta) {
    auto nablas = calculateNablas(miniBatch);
    auto learningRate = eta / miniBatch.size();

    // once nabla is known, adjust actual weights and biases
    for (auto segmentIndex = 0; segmentIndex < nablas.size(); ++segmentIndex) {
      auto nabla = nablas[segmentIndex];
      auto seg = mSegments[segmentIndex];
      seg->Mul(learningRate);
      seg->Sub(*nabla);
    }
  }
};

INetworkPtr NewNetwork(const std::vector<int>& layerSizes, INetworkMetadataPtr metadata) {
  std::shared_ptr<Network> sp(new Network(layerSizes, metadata));
  return INetworkPtr(sp);
}

// declare pure virtual dtor body
INetwork::~INetwork() {}
