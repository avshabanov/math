# cd math
# virtualenv .venv
# pip install numpy
# python .../calc.py

import numpy

# Nicely format 2D matrix
def printMatrix(label, m):
    print(label)
    print('\n'.join(['|' + (''.join(['{:6}'.format(item) for item in row]) + ' |')
              for row in m]))

# l1 designates 3-nodes values in a neural network hidden layer 1
l1 = [
        [2.5],
        [4],
        [1.2]
        ]

# w12 designates weights applied when transitioning from layer 1 to layer 2
w12 = [
        [  -1,  0.4,  1.5],
        [ 0.8,  0.5,  0.75],
        [ 0.2, -0.3,  1]
        ]

# l2 - layer 2 node values; dim = (1x3) * (3x3) = (1x3)
l2 = numpy.matmul(w12, l1)

# Straightforward value propagation
printMatrix('l1 * w12 = l2 =', l2)

# Node value scale matrix for layer 1
a = [
        [2.0, 0, 0],
        [0, 1, 0],
        [0, 0, 0.2]
        ]

# a_inv = a^(-1)
a_inv = numpy.linalg.inv(a)
printMatrix('a^(-1) =', a)

# l1' - covariant scale changes to nodes in l1
l1_cov = numpy.matmul(a, l1)
printMatrix("l1' = ", l1_cov)

# w12' - new weights, contravariant tensor to the l1 node changes (l1')
w12_contv = numpy.matmul(w12, a_inv)
printMatrix("w12' = ", w12_contv)

# illustration of the tensor invariant:
l2_copy = numpy.matmul(w12_contv, l1_cov)
printMatrix("l2 = l1' * w12'", l2_copy)


