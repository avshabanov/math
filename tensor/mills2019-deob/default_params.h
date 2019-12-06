// This is needed to let IDE correlate preprocessor parameters in main.c against their default values.
#pragma once

/*
Hyperparameters:
*/

#define RS  0.15
#define TR  0.95
#define LR  0.002
#define LD  0.97
#define LE  10
#define CL  5
#define B1  0.9
#define B2  0.999
#define EP  1e-8
#define WD  8e-5
#define DI  100
#define SL  200
#define N   50
#define TP  1
#define PF  '"cp%02d_%.3f"'

/*
RNN layout:
*/

#define HS 128

#define BK  \
  hp = I(HS),                         \
  t1 = L(HS, x),                      \
  h  = C(hp, T(A(t1, L(HS, hp)))),    \
  y  = h

#define NW  \
  x   = I(n),                         \
  y   = L(n, MD(x))
