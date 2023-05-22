import numpy as np
import matplotlib.pyplot as plt

def TchebychevExtremas(n:int, interA:float, interB:float):
    lAbs = [np.cos(i*np.pi/(n-1)) for i in range(0,n)] # [-1;1], extremas
    return list(map(lambda x: (x+1.0)/2.0*(interB-interA)+interA, lAbs)) # [0;1] -> [a;b]

# degre of polynomial is n
def remes(f, interA:float, interB:float, n:int, precision:int = 1000, maxIter:int = 200):
    lAbsAll = np.linspace(interA, interB, num=precision)
    lImgAll = np.array(list(map(f, lAbsAll)))
    valTcheby = np.flip(TchebychevExtremas(n+2, interA, interB)) # n+2 points and sorted in ascending

    # Know where are roots in lAbsAll 
    iTchebychev = []
    rootToFind = 0
    iRoot, valRoot = 0, lAbsAll[0]

    for i,e in enumerate(lAbsAll[1:]):
        if abs(valTcheby[rootToFind]-e) < abs(valTcheby[rootToFind]-valRoot):
            valRoot = e
            iRoot = i+1
        elif valTcheby[rootToFind]-e < 0: # Roots are increasing, so we pass to the next one
            iTchebychev.append(iRoot)
            rootToFind += 1
    if len(iTchebychev) != n+2:
        iTchebychev.append(precision-1)

    # We define epsilon (in informatic) to measure the error     
    error = 0.0
    epsilon = 1.0 + np.finfo(np.float64).eps

    for i in range(maxIter):
        # We have to find the coefficients of the polynomial of degree n
        # Go to resolve the system of equations
        vandermonde = np.array([[x**j for j in range(n+1)] + [(-1)**i] for i,x in enumerate(lAbsAll[iTchebychev])])
        x = np.linalg.solve(vandermonde, lImgAll[iTchebychev])
        coeff = x[:-1] # coefficients of the polynomial
        p_n = lambda x : sum(coefficient*np.power(x, i) for i, coefficient in enumerate(coeff))
        # x[-1] estimation of error (e)
        if abs(x[-1]) < epsilon*error:
            return p_n
        error = abs(x[-1])

        lError = lImgAll - p_n(lAbsAll)
        iMaxError = np.argmax(abs(lError))  # index of abscissa of the point with the max error
        
        # We exchange value to create an equioscillating error
        roll = False
        if iMaxError < iTchebychev[0]:
            if lError[iMaxError] * lError[iTchebychev[0]] < 0: # Not the same sign
                roll = True
            iTchebychev = [iMaxError] + iTchebychev[:-1] if roll else [iMaxError] + iTchebychev[1:]
        elif iMaxError > iTchebychev[-1]:
            if lError[iMaxError] * lError[iTchebychev[-1]] < 0:
                roll = True
            iTchebychev = iTchebychev[1:] + [iMaxError] if roll else iTchebychev[:-1] + [iMaxError]
        else:
            for i in range(len(iTchebychev)-1):
                if iTchebychev[i] <= iMaxError <=iTchebychev[i+1] :
                    if lError[iMaxError] * lError[iTchebychev[i]] >= 0: # Same sign
                        iTchebychev[i] = iMaxError
                    else:
                        iTchebychev[i+1] = iMaxError
                    break

# * Init
interA = -1.0
interB = 10
precision = 1000
deg = 15
maxIter = 200

X = np.linspace(interA, interB, precision)
# f = lambda x : np.exp(x) # deg = 3 to see anything, that's approximate very well !

# * Fonction marrante, n=20 on voit le phénomène d'imprécision, [-1,15] par exemple
f = lambda x : np.cos(3*x)*np.sin(x)**2-np.log(2+x**2)
rem =  remes(f, interA, interB, deg, precision=precision, maxIter = 150)(X)

# Curiosity. You can delete this !
# ? Taylor comparison 
isTaylor = False
def expTaylor(x):
    res = 0
    for i in range(deg+1):
        res += x**i/np.math.factorial(i)
    return res
txtTaylor = ", comparison with Taylor" if isTaylor else ""

# * Plots
# ? Main plot
plt.subplot(211)
plt.gca().set_title("Remes Algorithm, deg = "+ str(deg)+txtTaylor)
plt.plot(X, f(X), c="black", label="f(x)")
plt.plot(X,rem, c="r", label="Remes")
if isTaylor:
    plt.plot(X, expTaylor(X), c="b", label="Taylor")
plt.legend()

# ? Error
plt.subplot(212)
plt.gca().set_title("Error")
plt.plot(X, f(X)-rem, c="r", label="Remez")
plt.plot(X, [0]*len(X),'--',c='black', label="y=0")
plt.plot(X, [np.max(f(X)-rem)]*len(X),'--', c='orange', label="max error")
plt.plot(X, [-np.max(f(X)-rem)]*len(X),'--', c='orange', label="min error")
if isTaylor:
    plt.plot(X, f(X)-expTaylor(X), c="b", label="Taylor")
plt.legend()

plt.show()
