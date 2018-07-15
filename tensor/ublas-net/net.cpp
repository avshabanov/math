#include <iostream>
#include <string>

#include "net.h"

#include <boost/numeric/ublas/matrix.hpp>
#include <boost/numeric/ublas/io.hpp>

namespace ub = boost::numeric::ublas;

using namespace std;

class Segment {
private:
  int mPreviousLayerSize;
  int mLayerSize;

public:
  Segment(int previousLayerSize, int layerSize) :
    mPreviousLayerSize(previousLayerSize),
    mLayerSize(layerSize) {
  }

  string String() {
    ostringstream ss;
    ss << "Layer#{prevLayerSize=" << mPreviousLayerSize << ", layerSize=" << mLayerSize << '}';
    return ss.str();
  }  
};

typedef shared_ptr<Segment> SegmentPtr;

class Network : public INetwork {
  vector<SegmentPtr> mSegments;

public:
  Network(const vector<int> layerSizes) {
    auto segmentCount = layerSizes.size() - 1;
    mSegments.reserve(segmentCount);

    for (auto i = 0; i < segmentCount; ++i) {
      SegmentPtr sp(new Segment(layerSizes.at(i), layerSizes.at(i + 1)));
      mSegments.push_back(sp);
    }
  }

  virtual ~Network() {
    cout << "disposing network" << endl;
  }

  virtual std::string String() {
    ostringstream ss;
    ss << "Layers:";
    for (auto it = mSegments.begin(); it != mSegments.end(); ++it) {
      ss << (it != mSegments.begin() ? ", " : " ");
      auto sp = *it;
      ss << ' ' << sp->String();
    }
    return ss.str();
  }
};

INetworkPtr NewNetwork(const std::vector<int> layerSizes) {
  std::shared_ptr<Network> sp(new Network(layerSizes));
  return static_pointer_cast<INetwork, Network>(sp);
}

// declare pure virtual dtor body
INetwork::~INetwork() {}
