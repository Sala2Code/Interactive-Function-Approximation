import tkinter
import customtkinter
from screeninfo import get_monitors

from matplotlib.backends.backend_tkagg import (FigureCanvasTkAgg, NavigationToolbar2Tk)
from matplotlib.backend_bases import key_press_handler
from matplotlib.figure import Figure
import numpy as np
from scipy.integrate import quad

from utility import *

# *----------------- Configuration -----------------*
# ! It's not dynamic, choose the size of your screen ! Else, some buttons can disappear
# ? Full screen
# widthScreen = get_monitors()[0].width
# heightScreen = get_monitors()[0].height
widthScreen = 1080
heightScreen = 720

customtkinter.set_appearance_mode("system")  
customtkinter.set_default_color_theme("dark-blue")  # Themes: blue (default), dark-blue, green

app = customtkinter.CTk() 
app.geometry(str(widthScreen)+"x"+str(heightScreen))
app.wm_title("Approximation de fonction par des polynomes")

# ? grid to place widgets
nbCol = 12
nbLine = 3
padding = 15
# paddingRelX = padding / widthScreen
paddingRelY = padding / heightScreen
heightButton = 30
heightSlider = 20

# * ----------------- Methods ----------------- *
def nothing(*args):
    return None

def updateSlider(*args):
    for i in methApprox:
        i[1](False) # False to avoid the update of the plot
    fig.gca().set_title("Approximation of "+ fStr + ", deg = "+str(int(slider.get())) )

def generalApprox(nMeth, title, color, methFunc, arg):
    global methActive
    if arg == ():
        # select the index of method and the first element, see "display"
        methActive[nMeth][0] = not methActive[nMeth][0] # Button (un)pressed

    if switchError.get() == "off":
        # ? Delete lines
        for i in fig.gca().lines:
            if i.get_label() == title:
                i.remove()
                break # to avoid losing time 


        if methActive[nMeth][0]: # If pressed
            # ? Calculate new approximation
            res = methFunc()
            fig.gca().plot(t, res, c=color, label=title)
            fig.gca().legend()

        canvas.draw()
    else:
        error()


def bernsteinApprox(*args):
    generalApprox(0, "Bernstein", "dodgerblue", bernsteinFunc, args)
def bernsteinFunc():
    n = int(slider.get())
    res = np.zeros_like(t)
    for k in range(n+1):
        res += f(k/n) * np.math.comb(n, k) * t**k * (1-t)**(n-k)
    return res


def remesApprox(*args):
    generalApprox(1, "Remes", "tomato", remesFunc, args)
def remesFunc(precision=1000, maxIter = 100):
    n = int(slider.get())
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
            return p_n(t)
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
    print("Error best approximation !")
    return p_n(t)


def fourierApprox(*args):
    generalApprox(2, "Fourier", "orchid", fourierFunc, args)
def fourierFunc():
    # it's not a polynome ! So the slider doesn't give his degree, just the approximation use trigonometric function where argument is iθ, with 1<=i<=n
    n = int(slider.get())
    L = interB - interA

    a0 = (1/L)*quad(f,interA,interB)[0]
    al = [(1/L)*quad(Acoeff,interA,interB,args=(f,i+1,L),limit=1000)[0] for i in range(0,n)]
    bl = [(1/L)*quad(Bcoeff,interA,interB,args=(f,i+1,L),limit=1000)[0] for i in range(0,n)]
    res = 0.5*a0
    for i in range(1,n+1):
        res += (al[i-1]*np.cos((i*np.pi*t)/L))+(bl[i-1]*np.sin((i*np.pi*t)/L))
    return res

# ! TODO
def symbolic(*args):
    return None

def error():
    fig.gca().clear()
    if switchError.get() == "on":
        fig.gca().plot(t, [0]*len(t), "--", c="black", label="f(x)=0")
        for i in methActive:
            if i[0]:
                valErr = f(t)-i[2]()
                fig.gca().plot(t, valErr)

        fig.gca().legend()
        canvas.draw()
    else:
        updatePlot(f, fStr, interA, interB)

def writeFunc():
    global f
    dialog = customtkinter.CTkInputDialog(text="Write the new function\n f(x) =", title="New function")
    # ! Code parser 
    fStr = str(dialog.get_input())
    f = lambda x : eval(fStr)
    updatePlot(f, fStr, interA, interB)

def changeInterA():
    global interA
    dialog = customtkinter.CTkInputDialog(text="First bound, A = ", title="New bound A")
    interA = float(dialog.get_input())
    updatePlot(f, fStr, interA, interB)
    buttonInterA.configure(text=str(interA))

def changeInterB():
    global interB
    dialog = customtkinter.CTkInputDialog(text="Second bound, B = ", title="New bound B")
    interB = float(dialog.get_input())
    updatePlot(f, fStr, interA, interB)
    buttonInterB.configure(text=str(interB))

def updatePlot(f, fStr, A, B):
    global t
    t = np.arange(A, B, pas) # Update the abscissa
    fig.gca().clear()
    fig.gca().plot(t, f(t), c="black", label=fStr)
    # set the limit of the plot to be centering the function approximate
    paddingPlot = 0.5*(max(f(t))-min(f(t)))
    fig.gca().set_ylim(min(f(t))-paddingPlot, max(f(t))+paddingPlot)
    for i in methActive: # See if the method is active
        if i[0]:
            i[1]()

    fig.gca().legend()
    canvas.draw()


# *----------------- Display -----------------*
# ? Buttons approximation

# list method and their function associated
methApprox = [
                ("Bernstein",bernsteinApprox),
                ("Remez", remesApprox),
                ("Fourier", fourierApprox), 
                ("...", nothing), 
                ("...", nothing), 
                ("...", nothing)
            ] 


for i, e in enumerate(methApprox): # Display
    text, func = e[0], e[1]
    button = customtkinter.CTkButton(master=app, text=text, command=func, height=heightButton)
    posX = (1+2*(i%2))/nbCol # 1 offset col + numCol (ratio : [0;1])
    posY = paddingRelY + heightButton/(2*heightScreen) + 2/3+(i//2)/(3*nbLine) # padding + half heightButton + 2/3 screen + numLine (ratio : [0;1])
    button.place(relx=posX, rely= posY, anchor=tkinter.CENTER)

# ? Slider
slider = customtkinter.CTkSlider(master=app, from_=1, to=20, number_of_steps=20,command=updateSlider, height=heightSlider)
slider.place(relx=0.5, rely= paddingRelY + heightSlider/(2*heightScreen) + 2/3, anchor=tkinter.CENTER)
slider.set(1)

# ? Buttons options
valSymbolic, valError = customtkinter.StringVar(value="off"), customtkinter.StringVar(value="off")
switchSymbolic = customtkinter.CTkSwitch(master=app, text="Symbolic", command=symbolic, variable=valSymbolic, onvalue="on", offvalue="off")
switchError = customtkinter.CTkSwitch(master=app, text="Error", command=error, variable=valError, onvalue="on", offvalue="off")
methOption = [switchSymbolic, switchError]
for i, switch in enumerate(methOption):
    posX = (5+2*(i%2))/nbCol # 1 offset col + numCol (ratio : [0;1])
    posY = paddingRelY + heightButton/(2*heightScreen) + 2/3+(1+i//2)/(3*nbLine) # padding + half heightButton + 2/3 screen + numLine (ratio : [0;1])
    switch.place(relx=posX, rely= posY, anchor=tkinter.CENTER)



# ? Function inputs
button = customtkinter.CTkButton(master=app, text="f(x)", command=writeFunc,width=250, height=heightButton) # 'ai pas réussi à mettre du latex, en même temps c'est récent donc faut l'implétenter à la mano je pense. Après c'est pas si utile.
button.place(relx=0.8, rely= 2/3 + heightButton/heightScreen, anchor=tkinter.CENTER)

buttonInterA = customtkinter.CTkButton(master=app, text="0", command=changeInterA, height=heightButton)
buttonInterA.place(relx=0.72, rely= (2*nbLine+1)/(3*nbLine) + heightButton/heightScreen, anchor=tkinter.CENTER)

buttonInterB = customtkinter.CTkButton(master=app, text="4", command=changeInterB, height=heightButton)
buttonInterB.place(relx=0.9, rely=(2*nbLine+1)/(3*nbLine) + heightButton/heightScreen, anchor=tkinter.CENTER)



# ? Plot
# * Init
interA, interB, pas = 0, 4, 0.01
methActive = [  # isActivate, approx, func
                [False, bernsteinApprox, bernsteinFunc],
                [False, remesApprox, remesFunc],
                [False, fourierApprox, fourierFunc],
            ] 


# f = lambda x : np.sin(2*x)
# fStr = r"$f(x) = sin(2x)$"
f = lambda x :  np.cos(3*x)*np.sin(x)+np.log(x**2+1)
fStr = r"$f(x) = cos(3x)*sin(x)+ln(x^2+1)$"

fig = Figure()
t = np.arange(interA, interB, pas)
fig.add_subplot(111).plot(t, f(t), c="black", label=fStr)
fig.gca().set_xlim(interA, interB)
paddingPlot = 0.5*(max(f(t))-min(f(t)))
fig.gca().set_ylim(min(f(t))-paddingPlot, max(f(t))+paddingPlot) 
fig.gca().set_title("Approximation of "+ fStr + ", deg = "+str(int(slider.get())) )
fig.gca().legend()

canvas = FigureCanvasTkAgg(fig, master=app)
canvas.draw()
# canvas.get_tk_widget().config(height=2*heightScreen/3) 
canvas.get_tk_widget().pack(side=tkinter.TOP, fill=tkinter.BOTH)

app.mainloop()
