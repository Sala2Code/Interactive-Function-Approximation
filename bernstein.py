from sympy import Symbol, simplify, collect, expand
from sympy import binomial, Rational, exp, sin, ln

x = Symbol('x')
N = Symbol('N')

def bernstein_poly(fun, n):

    return sum(fun(Rational(k, n)) * binomial(n, k) * x**k * (1 - x)**(n - k) for k in range(0, n + 1))

print(bernstein_poly(lambda x: x**N, 10).simplify())
#print(bernstein_poly(lambda t: exp(t) * sin(2 * t) + 3 * ln(1 + t) - ln(3 - t), 3).collect())
print(collect(expand(bernstein_poly(lambda t: exp(t) * sin(2 * t) + 3 * ln(1 + t) - ln(3 - t), 3)), x))
