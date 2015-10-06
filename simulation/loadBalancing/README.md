
# Overview

Application that illustrates simulation of load balancing strategies:

* Full knowledge-distribution
* Random distribution
* Random pick-compare distribution

# Simulation Results

```
Starting simulation using load balancing strategy=ExactDistributionLoadBalancerStrategy
Feeding 1000 units of work. Load: p100=50.0%, p99=50.0%, p90=50.0%, p50=50.0%
Feeding 1000 units of work. Load: p100=50.0%, p99=50.0%, p90=50.0%, p50=50.0%
Feeding 1000 units of work. Load: p100=50.0%, p99=50.0%, p90=50.0%, p50=50.0%
Feeding 1000 units of work. Load: p100=50.0%, p99=50.0%, p90=50.0%, p50=50.0%
Feeding 1000 units of work. Load: p100=50.0%, p99=50.0%, p90=50.0%, p50=50.0%
Feeding 0 units of work. Load: p100=0.0%, p99=0.0%, p90=0.0%, p50=0.0%
Feeding 2000 units of work. Load: p100=100.0%, p99=100.0%, p90=100.0%, p50=100.0%
Feeding 2000 units of work. Load: p100=100.0%, p99=100.0%, p90=100.0%, p50=100.0%
Feeding 2000 units of work. Load: p100=100.0%, p99=100.0%, p90=100.0%, p50=100.0%
Feeding 2000 units of work. Load: p100=100.0%, p99=100.0%, p90=100.0%, p50=100.0%
Feeding 2000 units of work. Load: p100=100.0%, p99=100.0%, p90=100.0%, p50=100.0%
Feeding 3000 units of work. Load: p100=150.0%, p99=150.0%, p90=150.0%, p50=150.0%
Feeding 0 units of work. Load: p100=50.0%, p99=50.0%, p90=50.0%, p50=50.0%
Feeding 0 units of work. Load: p100=0.0%, p99=0.0%, p90=0.0%, p50=0.0%
End of simulation, strategy=ExactDistributionLoadBalancerStrategy
---

Starting simulation using load balancing strategy=RandomLoadBalancerStrategy
Feeding 1000 units of work. Load: p100=118.0%, p99=112.0%, p90=110.0%, p50=58.0%
Feeding 1000 units of work. Load: p100=114.0%, p99=114.0%, p90=112.0%, p50=55.0%
Feeding 1000 units of work. Load: p100=140.0%, p99=130.0%, p90=110.0%, p50=58.0%
Feeding 1000 units of work. Load: p100=150.0%, p99=118.0%, p90=110.0%, p50=58.0%
Feeding 1000 units of work. Load: p100=142.0%, p99=134.0%, p90=122.0%, p50=62.0%
Feeding 0 units of work. Load: p100=42.0%, p99=34.0%, p90=22.0%, p50=0.0%
Feeding 2000 units of work. Load: p100=204.0%, p99=204.0%, p90=204.0%, p50=115.0%
Feeding 2000 units of work. Load: p100=326.0%, p99=322.0%, p90=308.0%, p50=119.0%
Feeding 2000 units of work. Load: p100=434.0%, p99=432.0%, p90=416.0%, p50=122.0%
Feeding 2000 units of work. Load: p100=552.0%, p99=536.0%, p90=526.0%, p50=115.0%
Feeding 2000 units of work. Load: p100=642.0%, p99=642.0%, p90=640.0%, p50=118.0%
Feeding 3000 units of work. Load: p100=848.0%, p99=826.0%, p90=800.0%, p50=174.0%
Feeding 0 units of work. Load: p100=748.0%, p99=726.0%, p90=700.0%, p50=74.0%
Feeding 0 units of work. Load: p100=648.0%, p99=626.0%, p90=600.0%, p50=0.0%
End of simulation, strategy=RandomLoadBalancerStrategy
---

Starting simulation using load balancing strategy=RandomPickCompareLoadBalancerStrategy
Feeding 1000 units of work. Load: p100=58.0%, p99=58.0%, p90=58.0%, p50=54.0%
Feeding 1000 units of work. Load: p100=57.0%, p99=56.0%, p90=56.0%, p50=54.0%
Feeding 1000 units of work. Load: p100=60.0%, p99=58.0%, p90=58.0%, p50=56.0%
Feeding 1000 units of work. Load: p100=56.0%, p99=56.0%, p90=56.0%, p50=54.0%
Feeding 1000 units of work. Load: p100=60.0%, p99=58.0%, p90=58.0%, p50=56.0%
Feeding 0 units of work. Load: p100=0.0%, p99=0.0%, p90=0.0%, p50=0.0%
Feeding 2000 units of work. Load: p100=116.0%, p99=116.0%, p90=114.0%, p50=112.0%
Feeding 2000 units of work. Load: p100=126.0%, p99=126.0%, p90=126.0%, p50=124.0%
Feeding 2000 units of work. Load: p100=142.0%, p99=142.0%, p90=141.0%, p50=140.0%
Feeding 2000 units of work. Load: p100=156.0%, p99=154.0%, p90=152.0%, p50=150.0%
Feeding 2000 units of work. Load: p100=162.0%, p99=162.0%, p90=161.0%, p50=159.0%
Disconnected from the target VM, address: '127.0.0.1:53400', transport: 'socket'
Feeding 3000 units of work. Load: p100=228.0%, p99=228.0%, p90=228.0%, p50=224.0%
Feeding 0 units of work. Load: p100=128.0%, p99=128.0%, p90=128.0%, p50=124.0%
Feeding 0 units of work. Load: p100=28.0%, p99=28.0%, p90=28.0%, p50=24.0%
End of simulation, strategy=RandomPickCompareLoadBalancerStrategy
---
```