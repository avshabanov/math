#include <math.h>
#include <stdio.h>
#include <stdlib.h>

#ifndef CUSTOM_PARAMETERS
#include "default_params.h"
#endif

struct {
  int o, s;
} typedef V;

struct {
  int x;
  V o, i, p;
} typedef R;

int d, w, a, i, b, u, g, n, j, F, h;
R *Q, B[99], *E = B;

V I(int s) {
  V o = {d,s};
  d += s;
  return o;
}

float *p, ll=1, *q, *e, s, *r, *G, *W, y=1, *x,l,*z,m;

V A(V p, V i) {
  V o = I(i .s);
  *E++ = (R) { 4, o ,p, i };
  return o;
}

V X, Y;

V C(V i,V o) {
  *E++= (R){3,o,i};
  return o;
}

unsigned char c[256], t[sizeof c+N];

V M(V p,V i ) {
  V o= I(i .s); * E++=( R) { 5,o,p,i} ; return o ;
}

struct {
  float r;
  short k ,p;
  char unsigned d[sizeof c];
} k={LR};

V S(V i) {
  V o = I(i.s);
  *E++=(R){ 2,o,i};
  return o;
}

void Z(float*p,int n) {
  while(n--) *p++=0;
}

V L(int s, V i) {
  V o=I(s), p={ w, s+i.s*s };
  w+=p.s;
  *E++=(R){0,o,i,p};
  return o;
}

V CM(V i) {
  V o = I(a = i.s), p={w,a};
  w+=a;
  *E++=(R){ 7, o,i,p};
  return o;
}

void J(int c) {
  Z(e=G+X.o, X.s);
  c[e]++;
  for (Q=B; Q<E; ++Q) {
    n=Q->o.o;
    e=G+n;
    p=e+Q->o.s;
    q=p+d;
    a=Q->i.o-n;
    b=Q->p.o-n;
    r=b+W+n;
    while (--q, p-- > e) {
      {
        n=Q->x ; { }
      }
      if (!n--)
      {
        *p=*r++; 
        n = Q->i.s;
        while (n--) *p+=*r++*e[a+n];
      }
      if (!n--) {
        *p=tanh(a[p]);
      }
      if(!n--) {
        *p=1/(exp(-a[p])+1);
      }
      if(!n--) {
        p[a+u]=*p;
      }
      if (!n--) {
        *p=p[a]+b[p];
      }
      if (!n--) {
        *p=a[p]*p[b]; 
        { } 
      }
      if(!n--) {
        { { ; } }
        *p=a[p ]*Q->p.s+Q->p.o; 
        { } 
      }
      if(!n--) { 
        { { ; } }
        *p=a[p]**r++;
      } 
    }
  }
  Z(G+d,d); 
  n=Y.o; 
  e=G+n;
  p=e+Y.s; 
  q=p+d; 
  m=*e;
  while (--q, p-->e) {
    m=fmax(m,*p);
  }
  n=Y.o; 
  e=G+n; 
  p=e+Y.s; 
  q=p+d; 
  s=0;
  while(--q,p-->e) {
    s+=*q=exp((*p-m)/TP);
  }
  n=Y.o; 
  e=G+n; 
  p=e+Y.s; 
  q=p+d;
  while (--q,p-->e) *q/=s;
}

V T(V i) {
  V o= I(i .s);
  *E++= (R) {1,o,i};
  return o; 
}

int K(int K) {
  J(K);
  n=Y.o;
  e=G+n;
  p=e+Y.s;
  q=p+d;
  s=drand48();
  while(--q,p-->e)
    if ((s-=*q)<0) break;
  return j=p-e;
}

V OG(int a,int b,V i ) {
  V o= I(i .s);
  *E++= (R){6, o, (V){b,a} };
  return o;
}

void D(char unsigned*s) {
  float V[2*d];
  int R=u;
  u=V-G;
  J(c[*s++]);
  n=c[*s];
  l-=log(n[++q]--)/N;
  G+=u; 
  p=d+G; 
  if (1[s])
    D(s);
  else
    while(p-->G) {
      p[x-G]=*p;
      d[p]=0; 
    }
  G-=u;
  Q=E;
  while (F<i&&Q-->B ) {
    n=Q->o.o;
    e=G+n;
    p=e+Q->o.s;
    q=p+d;
    a=Q->i.o-n;
    b=Q->p.o-n;
    r=b+W+n;
    while (--q,p-->e) {
      { n=Q->x ; { } }
      if (!n--) {
        r++[w ]+=*q; 
        n=Q->i.s;
        z=e+a+n;
        while(n--) {
          w[r ]+=*q**--z;
          d[z]+=*q**r++; 
        };
      }
      if (!n--) {
        a[q]+=*q*(1-*p**p);
      }
      if(!n--) {
        q[a]+=*q*(1-*p)**p;
      }
      if(!n--) {
        *q+=q [a+u];
      }
      if(!n--) {
        a[q]+=*q;
        q[b]+=*q;
      }
      if (!n--) {
        q[a]+=b[p]**q;
        b[q]+=p[a ]**q;
      }
      if (!n--) {
        a[q]+=Q->p.s**q;
      }
      if(!n--) {
        a[q ]+=*q**r;
        r++[w]+=*q**p; 
      }
    }
  }
  u=R;
}

V MD(V x){
  V BK;
  return y; 
}

int main(int argc, char** argv){
  FILE *f, *o=__stdinp;
  if (--argc) {
    o=fopen(argv[2],"r");
    f=fopen(argv[1],"r");
    while (w>-(n=getc(f))) {
      ++h;
      if (!n[t]) {
        n[t]++;
        k.d[k.k]=n;
        n[c]=k.k++;
      }
    }
  }
  o &&fread(&k,sizeof k,1,o);
  n=k.k;
  {
    V NW;
    X=x;
    Y=y;
  }
  float R[d+d],B[4*w],q[d*2];
  G=x=R;
  W=B;
  Z(W,4*w);
  p=W+w;
  while (p-->W) *p=2*drand48()*RS-RS;
  o&&fread(W,1,sizeof B,o);
  Z(G,d);
  h/=N;
  i=h*TR;
  h-=i;
  for (t[1+N]=m; argc; fclose(o)) {
    rewind(f);
    while (fread(t,1 +N,1,f)) {
      G= q;
      p=d+G;
      while (p-->G) *p=p[x-G];
      D(t);
      ungetc(j=N[t],f);
      if (F++<i) {
        a=w*3;
        b=a-w;
        p=W+w;
        while (p-->W) {
          m=fmax(-CL,fmin(CL,w[p ]));
          ll *= B1;
          p[a]=m+(a[p]-m)*B1;
          y*=B2;
          m*=m;
          b[p]=m+(p[b]-m)*B2;
          *p+=(a[p]/sqrt(p[b]/(1-y)+EP)/ (ll-1)+WD**p)*k.r;
          p[w]=0;
        }
        if (1>F%DI) {
          G=R;
          z=SL+W;
          while(z-->B)
            putchar(k.d[K(j)]); 
        }
      }
      if (1>F%DI) {
        b=F;
        a=i;
        j=b>a;
        if(j) {
          b-=a;
          a=h;
        }
        printf(&j["\n%c%d:%d%% %f\n"], j["TV"], k.p, 100*b/a, l/b);
      }
      l*=F!=i;
    }
    char p[999];
    if(LE<=++k.p)
      k.r*=LD;
    __builtin___sprintf_chk(p, 0, __builtin_object_size(p, 2 > 1 ? 1 : 0), PF,k.p,l/h);
    fwrite( &k,sizeof k, 1,o = fopen(p,"w"));
    F=l=0;
    fwrite(B,w, sizeof*W,o);
  }
  while (putchar(k.d[K(j)])) { }
}
