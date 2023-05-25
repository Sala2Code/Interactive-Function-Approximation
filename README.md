# Interactive-Function-Approximation
Interactive approximation of continuous functions using Remes, Bernstein, and Fourier methods

## main.py
The main file contains the interactive plot. You can modify abscissas, function, approximation methods, change the degree of approximation, look error wtih the function and see the difference between numerical computation and symbolic.

<p align="center">
  <img src="https://github.com/Sala2Code/Interactive-Function-Approximation/assets/109032171/050ec754-812a-4e81-af05-54a54145b528" alt="InteractiveApproximation py">
</p>



To modify the new function, write in python. If you want $\sqrt{cos(x^2)}$ you have to write : np.cos(x*\*2)*\*(0.5).
Maybe, a parser LaTeX will be there like a warning when you put an undefined function ($\frac{1}{x}$ on $[-1;1]$). The code continues to well works in despite of this lack.

We add Fourier Method, but the result is not a polynomial ! So, when you update the slider, keep in mind, we change argument in trigonometric function. His form is iθ with 1≤i≤n  We add that to personal pleasure! No comments are written in the report.

## UniformApproximation.pdf
Then, it's a scholar project. We made a more of 15 pages project titled "Approximation uniforme de fonctions continues : aspects analytique, algébrique et numérique" explaining how works approximation. The initial subject is about Bernstein Polynomials to then find out the reason why that's approximate and to finish on the Remes algorithm, to get the best polynomial approximation (and that's work very well, try on the code !)

## remes.py / remes.jl
If you interested by Remes Alogrithm, a code has been separated to a better handling. And even in 2 langages : Python and Julia.

Julia, $f(x)=cos(3x)\*sin(x)^2-ln(2+x^2)$:
<p align="center">
  <img src="https://github.com/Sala2Code/Interactive-Function-Approximation/assets/109032171/6d862a49-8903-4a4a-abcd-c5bd381968d7" alt="Remes jl">
</p>


Python, $f(x) = e^x$, I compare with Taylor Young approximation:
<p align="center">
  <img src="https://github.com/Sala2Code/Interactive-Function-Approximation/assets/109032171/26c0f6ce-965e-4e9e-9a66-79408bc85938" alt="Remes py">
</p>

## Interpolator.py / Interpolator.jl
There is equally, in these 2 langages, an interpolator code : interpolator ; that's compare equidistants nodes and Tchebychev nodes.
The historical example :
<p align="center">
  <img src="https://github.com/Sala2Code/Interactive-Function-Approximation/assets/109032171/3425e7dc-6d14-4b51-9d2f-ba61fdba93e4" alt="Interpolator jl">
</p>

## Lean
And to conclude, we wirte some definitions and try to prove some basics theorems, propositions, lemmas with Lean about algebra and analysis.
See the Lean folder. 
