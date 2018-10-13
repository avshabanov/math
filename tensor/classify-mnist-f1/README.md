# MNIST Neural-Network Based Classifier

This code is a java-to-python translation of code at http://neuralnetworksanddeeplearning.com/chap1.html using float numbers only.

## Notes

* [ReLU vs Sigmoid, Softmax and Tanh](https://algorithmsdatascience.quora.com/ReLu-compared-against-Sigmoid-Softmax-Tanh)

## Performance

### Mac Book Pro


```
Oracle JDK 1.8.0_20

Read 60000 image(s)
Epoch 0 took 10754ms to complete
Epoch 1 took 10179ms to complete
Epoch 2 took 10079ms to complete
Epoch 3 took 10184ms to complete
Epoch 4 took 10217ms to complete
Epoch 5 took 10353ms to complete
Epoch 6 took 10205ms to complete
Epoch 7 took 10100ms to complete
Epoch 8 took 10268ms to complete
Epoch 9 took 10148ms to complete
Epoch 10 took 10178ms to complete
Epoch 11 took 10293ms to complete
Epoch 12 took 10357ms to complete
Epoch 13 took 10646ms to complete
Epoch 14 took 10466ms to complete
Epoch 15 took 10340ms to complete
Epoch 16 took 10475ms to complete
Epoch 17 took 10453ms to complete
Epoch 18 took 10287ms to complete
Epoch 19 took 10324ms to complete
Epoch 20 took 10356ms to complete
Epoch 21 took 10321ms to complete
Epoch 22 took 10536ms to complete
Epoch 23 took 10745ms to complete
Epoch 24 took 10381ms to complete
Epoch 25 took 10346ms to complete
Epoch 26 took 10287ms to complete
Epoch 27 took 10546ms to complete
Epoch 28 took 10266ms to complete
Epoch 29 took 10227ms to complete
Test network:
Image #0, expected label: 5
	Got output=[0.00, 0.00, 0.00, 0.00, 0.00, 1.00, 0.00, 0.00, 0.00, 0.00], expected=[0.00, 0.00, 0.00, 0.00, 0.00, 1.00, 0.00, 0.00, 0.00, 0.00]
Image #1, expected label: 0
	Got output=[1.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00], expected=[1.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00]
Image #2, expected label: 4
	Got output=[0.00, 0.00, 0.00, 0.00, 1.00, 0.00, 0.00, 0.00, 0.00, 0.00], expected=[0.00, 0.00, 0.00, 0.00, 1.00, 0.00, 0.00, 0.00, 0.00, 0.00]
Image #3, expected label: 1
	Got output=[0.00, 1.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00], expected=[0.00, 1.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00]
Image #4, expected label: 9
	Got output=[0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.01, 0.00, 0.00], expected=[0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 1.00]
Image #5, expected label: 2
	Got output=[0.00, 0.00, 1.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00], expected=[0.00, 0.00, 1.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00]
Image #6, expected label: 1
	Got output=[0.00, 1.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00], expected=[0.00, 1.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00]
Image #7, expected label: 3
	Got output=[0.00, 0.00, 0.00, 1.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00], expected=[0.00, 0.00, 0.00, 1.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00]
Image #8, expected label: 1
	Got output=[0.00, 1.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00], expected=[0.00, 1.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00, 0.00]
Image #9, expected label: 4
	Got output=[0.00, 0.00, 0.00, 0.00, 1.00, 0.00, 0.00, 0.00, 0.00, 0.00], expected=[0.00, 0.00, 0.00, 0.00, 1.00, 0.00, 0.00, 0.00, 0.00, 0.00]
Match quality: 88.73 percent(s)
```

Record precision: 98.31% (which is exceptionally great!).