#include "net.h"

#include <functional>
#include <random>
#include <cmath>

using namespace std;

INetworkMetadata::~INetworkMetadata() {}

class LogisticFunctionBasedNetworkMetadata : public INetworkMetadata {
  mt19937 mRng;
  normal_distribution<float> mNormalDistr;

  inline float randomGaussian() {
    return mNormalDistr(mRng);
  }

  static inline float sigmoid(float x) {
    return 1.0f / (1.0f + (float) exp(-x));
  }

  static inline float sigmoidPrime(float x) {
    // first derivative of the logistics function: s'(x) = s(x) * (1 - s(x))
    auto v = sigmoid(x);
    return v * (1.0f - v);
  }
public:
  LogisticFunctionBasedNetworkMetadata() : mRng(), mNormalDistr(0.0f, 1.0f) {
  }

  virtual ~LogisticFunctionBasedNetworkMetadata() {
  }

  virtual void RandFill(float_array& arr) {
    for (auto i = 0; i < arr.size(); ++i) {
      arr[i] = randomGaussian();
    }
  }

  virtual void CalcSigmoid(float_array& arr) {
    for (auto i = 0; i < arr.size(); ++i) {
      arr[i] = sigmoid(arr[i]);
    }
  }

  virtual void CalcSigmoidPrime(float_array& arr) {
    for (auto i = 0; i < arr.size(); ++i) {
      arr[i] = sigmoidPrime(arr[i]);
    }
  }
};

INetworkMetadataPtr NewLogisticFunctionBasedNetworkMetadata() {
  shared_ptr<LogisticFunctionBasedNetworkMetadata> sp(new LogisticFunctionBasedNetworkMetadata());
  return INetworkMetadataPtr(sp);
}
