import matplotlib
import matplotlib.pyplot as plt
from matplotlib.widgets import  RectangleSelector
import pylab
from data.constraint import Constraint
import numpy as np
import sympy

def __plot_constraints(parameters, region, color):
    for constraints in reversed(region):
        for c in constraints:
            xs = np.linspace(0,1,11)
            print(xs)
            ys = [sympy.solve(c.polynomial.subs(parameters[0],x))[0].evalf() for x in xs]

            print(ys)
            if c.relation == ">=" or c.relation == ">":
                plt.fill_between(np.array(xs,dtype=float), np.array(ys,dtype=float), 1, facecolor=color) 
            else:
                plt.fill_between(np.array(xs,dtype=float), 0, np.array(ys,dtype=float), facecolor=color) 
            pylab.ylim([0,1])
            pylab.xlim([0,1])
        

def plot_constraints(parameters, saferegion, badregion):
   __plot_constraints(parameters, saferegion, 'green')  
   __plot_constraints(parameters, badregion, 'red')
    


def __onselect(eclick, erelease):
  'eclick and erelease are matplotlib events at press and release'
  print(' startposition : (%f, %f)' % (eclick.xdata, eclick.ydata))
  print(' endposition   : (%f, %f)' % (erelease.xdata, erelease.ydata))
  print(' used button   : ', eclick.button)

def __toggle_selector(event):
    print(' Key pressed.')
    if event.key in ['Q', 'q'] and toggle_selector.RS.active:
        print (' RectangleSelector deactivated.')
        toggle_selector.RS.set_active(False)
    if event.key in ['A', 'a'] and not toggle_selector.RS.active:
        print (' RectangleSelector activated.')
        toggle_selector.RS.set_active(True)



    
def plot_results_bool(parameters, samples_qualitative):
    if len(parameters) == 2:
        fig = plt.figure()
        ax1 = fig.add_subplot(111)
        xValid = []
        yValid = []
        xInvalid = []
        yInvalid = []
        for (key,val) in samples_qualitative.items():
            if val:
                xValid.append(key[0])
                yValid.append(key[1])
            else:
                xInvalid.append(key[0])
                yInvalid.append(key[1])
                
        ax1.scatter(xValid,yValid, marker='o', c='green')
        ax1.scatter(xInvalid,yInvalid, marker='x', c='red')
        pylab.ylim([0,1])
        pylab.xlim([0,1])
        ax1.set_xlabel(str(parameters[0]))
        ax1.set_ylabel(str(parameters[1]))
        __toggle_selector.RS = RectangleSelector(ax1, __onselect, drawtype='line')
        plt.connect('key_press_event', __toggle_selector)
        plt.show()    

        
def plot_results_val(parameters, result):
     if len(parameters) == 2:
         
        x = []
        y = []
        z = []
        for (key,val) in result.items():
            x.append(key[0])
            y.append(key[1])
            z.append(val)

        cm = plt.get_cmap("RdYlGn")
        col = [cm(float(i)) for i in z]
        plt.scatter(x,y,s=30,c=col,marker='o')
        pylab.ylim([0,1])
        pylab.xlim([0,1])
        plt.show()
        
        