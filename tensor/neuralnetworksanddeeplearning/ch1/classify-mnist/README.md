# MNIST Neural-Network Based Classifier

This code is a java-to-python translation of code at http://neuralnetworksanddeeplearning.com/chap1.html

## Performance

### Mac Book Pro


```
Oracle JDK 1.8.0_20

Read 60000 image(s)
Epoch 0 complete, took 16430ms.
Epoch 1 complete, took 16073ms.
Epoch 2 complete, took 16006ms.
Epoch 3 complete, took 16076ms.
Epoch 4 complete, took 15837ms.
Epoch 5 complete, took 15869ms.
Epoch 6 complete, took 15866ms.
Epoch 7 complete, took 15868ms.
Epoch 8 complete, took 15862ms.
Epoch 9 complete, took 15928ms.
Epoch 10 complete, took 16143ms.
Epoch 11 complete, took 15856ms.
Epoch 12 complete, took 16255ms.
Epoch 13 complete, took 16022ms.
Epoch 14 complete, took 15913ms.
Epoch 15 complete, took 16013ms.
Epoch 16 complete, took 16070ms.
Epoch 17 complete, took 15865ms.
Epoch 18 complete, took 15969ms.
Epoch 19 complete, took 16013ms.
Epoch 20 complete, took 16111ms.
Epoch 21 complete, took 15937ms.
Epoch 22 complete, took 16093ms.
Epoch 23 complete, took 16136ms.
Epoch 24 complete, took 16042ms.
Epoch 25 complete, took 16112ms.
Epoch 26 complete, took 15938ms.
Epoch 27 complete, took 16096ms.
Epoch 28 complete, took 16022ms.
Epoch 29 complete, took 16123ms.
Test network:
Image #0, expected label: 5
	Got output=[0.00, 0.00, 0.00, 0.00, 0.00, 1.00, 0.00, 0.00, 0.00, 0.00], expected=[0.00, 0.00, 0.00, 0.00, 0.00, 1.00, 0.00, 0.00, 0.00, 0.00]
Image #1, expected label: 0
	Got output=[1.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00], expected=[1.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00]
Image #2, expected label: 4
	Got output=[0.00, 0.00, 0.00, 0.03, 0.00, 0.00, 0.00, 0.03, 0.00, 0.00], expected=[0.00, 0.00, 0.00, 0.00, 1.00, 0.00, 0.00, 0.00, 0.00, 0.00]
Image #3, expected label: 1
	Got output=[0.00, 1.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00], expected=[0.00, 1.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00]
Image #4, expected label: 9
	Got output=[0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 1.00], expected=[0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 1.00]
Image #5, expected label: 2
	Got output=[0.00, 0.00, 1.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00], expected=[0.00, 0.00, 1.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00]
Image #6, expected label: 1
	Got output=[0.00, 1.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00], expected=[0.00, 1.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00]
Image #7, expected label: 3
	Got output=[0.00, 0.00, 0.00, 1.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00], expected=[0.00, 0.00, 0.00, 1.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00]
Image #8, expected label: 1
	Got output=[0.00, 1.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00], expected=[0.00, 1.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00]
Image #9, expected label: 4
	Got output=[0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00], expected=[0.00, 0.00, 0.00, 0.00, 1.00, 0.00, 0.00, 0.00, 0.00, 0.00]
...

Match quality: 88.69 percent(s)
```