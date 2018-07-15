#include <iostream>

#include "net.h"

using namespace std;

// Entry point
int main(int argc, char** argv) {
  INetworkPtr n = NewNetwork({3, 2, 1});
  cout << "Network: " << n->String() << endl;
  return 0;
}

