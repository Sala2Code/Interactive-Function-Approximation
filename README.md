# Interactive-Function-Approximation
Interactive approximation of continuous functions using Remes, Bernstein, and Fourier methods

## Main.py
The main file contains the interactive plot. You can modify abscissas, function, approximation methods, change the degree of approximation, look error wtih the function and see the difference between numerical computation and symbolic.

[Image à mettre]

To modify the new function, write in python. If you want $\sqrt{cos(x^2)}$ you have to write : np.cos(x*\*2)*\*(0.5).
Maybe, a parser LaTeX will be there like an warning when you put an undefined function ($\frac{1}{x}$ on $[-1;1]$). The code continues to well works in despite of this lack.

## UniformApproximation.pdf
Then, it's a scholar project. We made a more of 15 pages project titled "Approximation uniforme de fonctions continues : aspects analytique, algébrique et numérique" explaining how works approximation. The initial subject is about Bernstein Polynomials to then find out the reason why that's approximate and to finish on the Remes algorithm, to get the best polynomial approximation (and that's work very well, try on the code !)

## Remes.py / Remes.jl
If you interested by Remes Alogrithm, a code has been separated to a better handling. And even in 2 langages : Python and Julia.

Julia, $f(x)=cos(3x)\*sin(x)^2-ln(2+x^2)$:
<p align="center">
  <img src="https://github.com/Sala2Code/Interactive-Function-Approximation/assets/109032171/6d862a49-8903-4a4a-abcd-c5bd381968d7" alt="Remes jl">
</p>


Python, $f(x) = e^x$, I compare with Taylor Young approximation:
<p align="center">
  <img src="https://github.com/Sala2Code/Interactive-Function-Approximation/assets/109032171/26c0f6ce-965e-4e9e-9a66-79408bc85938" alt="Remes jl">
</p>

## Interpolator.py / Interpolator.jl
There is equally, in these 2 langages, an interpolator code : interpolator ; that's compare equidistants nodes and Tchebychev nodes.
The historical example :
<p align="center">
  <img src="https://github.com/Sala2Code/Interactive-Function-Approximation/assets/109032171/3425e7dc-6d14-4b51-9d2f-ba61fdba93e4" alt="Remes jl">
</p>

## Lean
And to conclude, we wirte some definitions and try to prove some basics theorems, propositions, lemmas with Lean about algebra and analysis.
See the Lean folder. 
