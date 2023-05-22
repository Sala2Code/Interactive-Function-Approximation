using Plots
using LaTeXStrings

function lagrange(X, Y, x)
    n = length(X) # or Y, it must have the same shape !
    phi = ones(n, length(x)) # coeff
    for i in 1:n
        for j in 1:n
            if i != j
                phi[i,:] .*= (x .- X[j]) ./ (X[i] .- X[j])
            end
        end
    end
    return transpose( transpose(Array{Float64}(Y)) * Array{Float64}(phi) ) # Y seems have a wrong shape
end

f = x -> 1/(1+25*x^2)
a,b = -1,1
step = 0.01 # pas
x = a:step:b
degP = 15

X = [i/degP for i in 1:degP] # to set on [0,1]
X = (b-a)*X .+ a  # to set on [a,b]
Y = [i for i in f.(X)]
y = lagrange(X, Y, x)

plot(x, y, label="Lagrange (équidistants)", legend=:top)
scatter!(X, Y, label="Abscisses équidistantes")

XT = [cos((2*i-1)*pi/(2*degP)) for i in 1:degP] # set on [-1,1]
XT = (XT.+1)/2*(b-a) .+a  # set on [0,1] then on [-a,b]
YT = [i for i in f.(XT)]
yT = lagrange(XT, YT, x)

plot!(x, yT, label="Lagrange (Tchebychev)")
scatter!(XT, YT, label="Abscisses Tchebychev")

plot!(f, label=L"$f(x) = \frac{1}{1+25x^2}$")
# savefig("Interpolateur_Equi_Tchebychev.png")