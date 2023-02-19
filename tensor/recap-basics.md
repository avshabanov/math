# Backpropagation Equations

## Notations

Forward function:

$$
z^l = w^l a^{l-1} + b^l, a^l = \sigma(z^l)
$$

---

Simple cost function (a.k.a. a *loss* or *objective* function):

$$
C = \frac{\sum_x C_x}{n}
$$

$$
C = \frac{1}{2n} \sum_{x} || y(x) - a ||^2
$$

where $||x||$ is a vector length function.

---

Error: $\delta^l_j$.

---

Sigmoid / a.k.a. logistics function:

$$
\sigma(z) = \frac{1}{1 + e^{-z}}
$$

---

## Main Formulas

[BP1](http://neuralnetworksanddeeplearning.com/chap2.html), An equation for the error in the output layer:

$$
\delta^L = \nabla_a C \odot \sigma'(z^L)
$$

For quadratic cost: $\nabla_a C = a^L - y$, so in this case error for output layer becomes $\delta^L = (a^L - y) \odot \sigma'(z^L)$.

---

[BP2](http://neuralnetworksanddeeplearning.com/chap2.html), An equation for the error $\delta^l$ in terms of the error in the next layer $\delta^{l+1}$:

$$
\delta^l = ((w^{l+1})^T \delta^{l+1}) \odot \sigma'(z^l)
$$

---

[BP3](http://neuralnetworksanddeeplearning.com/chap2.html), An equation for the rate of change of the cost with respect to any bias in the network:

$$
\frac{\partial C}{\partial b^{l}_{j}} = \delta^l_j
$$

where $\frac{\partial C}{\partial b^{l}_{j}}$ is the rate of bias change.

---

[BP4](http://neuralnetworksanddeeplearning.com/chap2.html), An equation for the rate of change of the cost with respect to any weight in the network:

$$
\frac{\partial C}{\partial w^{l}_{j k}} = a^{l-1}_k \delta^l_j
$$
