using Plots
using Polynomials 

function TchebychevExtremas(n::Int64, interA::Float64, interB::Float64)::Array{Float64,1}
    return [(1.0+cos(k*pi/(n-1)))/2.0*(interB-interA)+interA for k in (n-1):-1:0] # extremas tchebychev + flip to get an ascending array
end

function remes(f::Function, interA::Float64, interB::Float64, n::Int64, precision::Int64 = 1000, maxIter::Int64 = 200) # ::Function
    lAbsAll = LinRange(interA, interB, precision)
    lImgAll = map(f, lAbsAll)
    valTcheby = TchebychevExtremas(n+2, interA, interB)
    
    # Know where are roots in lAbsAll 
    iTchebychev = Int[]
    rootToFind = 1
    iRoot, valRoot = 1, lAbsAll[1]

    for (i, e) in enumerate(lAbsAll[2:end]) # We know the first element
        if abs(valTcheby[rootToFind] - e) < abs(valTcheby[rootToFind] - valRoot)
            valRoot = e
            iRoot = i+1
        elseif valTcheby[rootToFind] - e<0
            push!(iTchebychev, iRoot)
            rootToFind += 1
        end
    end
    if length(iTchebychev) != n+2
        push!(iTchebychev, precision)
    end

    error = 0.0
    epsilon = 1.0+eps(Float64)
    for i in 1:maxIter
        # * This yields : [[a, b, c], [d, e, f], [g h i]]
        vandermonde = [ vcat([x^j for j in 0:n], [(-1)^(i-1)] ) for (i,x) in enumerate(lAbsAll[iTchebychev])]
        # * To resolve linear system (simple example, deg = 1) we need this :  [a b c; d e f; g h i]
        vandermonde = transpose(hcat(vandermonde...))
        X = vandermonde \ lImgAll[iTchebychev]

        coeff =  X[1:end-1]
        # * Vanilla method
        # p_n = x -> sum( map( enumerate(coeff)) do (i,coefficient) coefficient*x^(i-1) end )
        p_n = Polynomial(coeff)
        if abs(X[end]) < epsilon*error
            return p_n
        end
        error = abs(X[end])

        lError = lImgAll - p_n.(lAbsAll)
        iMaxError = argmax(abs.(lError))
        
        # We exchange value to create an equioscillating error
        roll = false
        if iMaxError < iTchebychev[1]
            if lError[iMaxError] * lError[iTchebychev[1]] < 0 # Not the same sign
                roll = true
            end
            iTchebychev = roll ? [iMaxError; iTchebychev[1:end-1]] : [iMaxError; iTchebychev[2:end]]
        elseif iMaxError > iTchebychev[end]
            if lError[iMaxError] * lError[iTchebychev[end]] < 0
                roll = true
            end
            iTchebychev = roll ? [iTchebychev[2:end]; iMaxError] : [iTchebychev[1:end-1]; iMaxError]
        else
            for i in 1:length(iTchebychev)-1
                if iTchebychev[i] <= iMaxError <= iTchebychev[i+1]
                    if lError[iMaxError] * lError[iTchebychev[i]] >= 0
                        iTchebychev[i] = iMaxError
                    else
                        iTchebychev[i+1] = iMaxError
                    end
                    break
                end
            end
        end
    end
    print("Erreur d'approximation...")
    return p_n
end

interA = -1.0
interB = 10.
precision = 1000
deg = 15
maxIter = 200

f = x -> cos(3*x)*sin(x)^2-log(2+x^2)

X = LinRange(interA, interB, precision)
p_n = remes(f, interA, interB, deg, precision, maxIter)


# * Plots
valF = f.(X)
valPn = p_n.(X)
valErr = valF-valPn

p1 = plot(X, valF, label="f(x)", title="Remes Algorithm, deg = $deg")
plot!(X, valPn, label="p_n")

p2 = plot(X, valErr, label="Error", title="Error")
hline!([0], c="black", linestyle=:dash, label="y=0")
hline!([maximum(valErr)], linestyle = :dash, label="max")
hline!([minimum(valErr)], linestyle = :dash, label="min")

plot(p1, p2, layout = (2,1))
