Order Book Sample
=================

# Overview

Java solution to [rgmadvisors's](www.rgmadvisors.com/problems/orderbook/) order book problem.

# How to build

Run ``mvn package`` in the app folder. It will create a jar in the target directory.

# How to test

Once jar is built, run the following in the project folder:

```
cat sample/price0.txt | java -jar target/order-book-1.0-SNAPSHOT.jar 200
```

it should produce the following output:

```
28800758 S 8832.56
28800796 S NA
28800812 S 8832.56
28800974 B 8865.00
28800975 B NA
28812071 S NA
28813129 S 8806.50
28813300 S NA
28813830 B 8845.00
28814087 B 8836.00
28815804 S 8804.25
28815937 B 8845.00
28816245 B 8840.00
```

## How to analyze Pricer dataset

Target Size ``1``:

```
gzcat ~/Downloads/pricer.in.gz | java -jar target/order-book-1.0-SNAPSHOT.jar 1 > /tmp/out.1.txt
```

Target Size ``200``:

```
gzcat ~/Downloads/pricer.in.gz | java -jar target/order-book-1.0-SNAPSHOT.jar 200 > /tmp/out.200.txt
```

Target Size ``10000``:

```
gzcat ~/Downloads/pricer.in.gz | java -jar target/order-book-1.0-SNAPSHOT.jar 10000 > /tmp/out.10000.txt
```

Then compare with sample output datasets, e.g.:

```
gzcat ~/Downloads/pricer.out.10000.gz > /tmp/expected-out.10000.txt
diff /tmp/expected-out.10000.txt /tmp/out.10000.txt
```
