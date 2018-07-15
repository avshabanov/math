#pragma once

#include <vector>
#include <string>
#include <memory>

struct INetwork {
  virtual ~INetwork() = 0;
  virtual std::string String() = 0;
};

typedef std::shared_ptr<INetwork> INetworkPtr;

INetworkPtr NewNetwork(const std::vector<int> layerSizes);
