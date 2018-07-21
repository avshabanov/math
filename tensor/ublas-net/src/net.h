#pragma once

#include <vector>
#include <string>
#include <memory>

#include <boost/numeric/ublas/storage.hpp>

typedef boost::numeric::ublas::unbounded_array<float> float_array;
typedef std::vector<float> float_vector;

struct INetworkMetadata {
  virtual ~INetworkMetadata() = 0;

  virtual void RandFill(float_array& arr) = 0;

  virtual void CalcSigmoid(float_array& arr) = 0;

  virtual void CalcSigmoidPrime(float_array& arr) = 0;
};

struct TrainingData {
  float_vector input;
  float_vector output;

  TrainingData(const float_vector& in, const float_vector& out) : input(in), output(out) {
  }
};

typedef std::shared_ptr<INetworkMetadata> INetworkMetadataPtr;

INetworkMetadataPtr NewLogisticFunctionBasedNetworkMetadata();

struct INetwork {
  virtual ~INetwork() = 0;

  virtual std::string String() = 0;

  virtual float_vector Evaluate(const float_vector& input) = 0;

  virtual void SGD(
    const std::vector<TrainingData>& trainingSet,
    size_t epochs,
    size_t miniBatchSize,
    float eta,
    bool reportEpoch = false
  ) = 0;
};

typedef std::shared_ptr<INetwork> INetworkPtr;

INetworkPtr NewNetwork(const std::vector<int>& layerSizes, INetworkMetadataPtr metadata);
