import numpy as np

def TchebychevExtremas(n:int, interA:float, interB:float):
    lAbs = [np.cos(i*np.pi/(n-1)) for i in range(0,n)] # [-1;1], extremas
    return list(map(lambda x: (x+1.0)/2.0*(interB-interA)+interA, lAbs)) # [0;1] -> [a;b]

def Acoeff(x,f,n,L):
    return f(x)*np.cos((n*np.pi*x)/L)
def Bcoeff(x,f,n,L):
    return f(x)*np.sin((n*np.pi*x)/L)
