from matplotlib import pyplot as plt
import numpy as np
 
# naive method
def lagrange_bad(x,X,Y):
  n = min(len(X),len(Y))
  m = len(x)  
  Yh = np.zeros(m)
  phi = np.zeros(n)  
  for i in range(m):
    for j in range(n):
      phi[j] = 1.0
      for k in range(n):
        if j != k:
          phi[j] = phi[j]*(x[i]-X[k])/(X[j]-X[k])
      Yh[i] += Y[j] * phi[j]
  return Yh

# better method
def lagrange(x,X,Y):
  n = min(len(X),len(Y)) # same length normally
  phi = np.ones((n,len(x))) 
  for i in range(n):
    for j in range(n):
      if j!=i:
        phi[i,:] *= (x-X[j])/(X[i]-X[j])
      
  return Y @ phi # (1, N) X (N, x) = (1, x)


degP = 12
interA = -1
interB = 1
precision = 2000
f = lambda x : 1/(1 + 25*x**2)

x = np.linspace(interA,interB,precision)
X = np.linspace(interA,interB,degP)
Xtcheb = np.array([np.cos((2*i-1)*np.pi/(2*degP)) for i in range(1,degP+1)]) # set on [-1,1]
Xtcheb = (Xtcheb+1)/2*(interB-interA)+interA  # set on [0,1] then on [-a,b]

Yeq = f(X)
Ytcheb = f(Xtcheb)

plt.figure('Interpolation polynomiale')
plt.scatter(X,Yeq,label='Abscisses équidistantes')
plt.scatter(Xtcheb,Ytcheb,label='Abscisses de Tchebychev')

plt.plot(x, f(x), label='f(x)')
plt.plot(x, lagrange(x, X, Yeq), label="Lagrange (Tchebychev)")
plt.plot(x, lagrange(x, Xtcheb, Ytcheb), label="Lagrange (équidistants)")

plt.legend()
plt.show()
 