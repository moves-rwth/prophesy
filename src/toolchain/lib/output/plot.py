import pylab
import numpy
import sympy
from matplotlib import pyplot
from matplotlib import patches
from matplotlib.colors import ColorConverter

class Plot(object):
    def __plot_constraints(self, parameters, region, color):
        for constraints in reversed(region):
            for c in constraints:
                xs = numpy.linspace(0,1,11)
                print(xs)
                ys = [sympy.solve(c.polynomial.subs(parameters[0],x))[0].evalf() for x in xs]

                print(ys)
                if c.relation == ">=" or c.relation == ">":
                    pyplot.fill_between(numpy.array(xs,dtype=float), numpy.array(ys,dtype=float), 1, facecolor=color)
                else:
                    pyplot.fill_between(numpy.array(xs,dtype=float), 0, numpy.array(ys,dtype=float), facecolor=color)
                pylab.ylim([0,1])
                pylab.xlim([0,1])


    def plot_constraints(self, parameters, saferegion, badregion):
        self.__plot_constraints(parameters, saferegion, 'green')
        self.__plot_constraints(parameters, badregion, 'red')


    def __onselect(self, eclick, erelease):
        'eclick and erelease are matplotlib events at press and release'
        print(' startposition : (%f, %f)' % (eclick.xdata, eclick.ydata))
        print(' endposition   : (%f, %f)' % (erelease.xdata, erelease.ydata))
        print(' used button   : ', eclick.button)

    def __toggle_selector(self, event):
        print(' Key pressed.')
        if event.key in ['Q', 'q'] and toggle_selector.RS.active:
            print (' RectangleSelector deactivated.')
            toggle_selector.RS.set_active(False)
        if event.key in ['A', 'a'] and not toggle_selector.RS.active:
            print (' RectangleSelector activated.')
            toggle_selector.RS.set_active(True)


    @staticmethod
    def plot_results(parameters, samples_qualitative, anchor_points = [], additional_arrows = [], additional_lines = [], additional_boxes_green = [], additional_boxes_red = [], additional_boxes_blue = [], path_to_save=None, display=False):
        if len(parameters) == 2:
            fig = pyplot.figure()
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

            for (anchor_points_for_a_dir, pos_x, pos_y) in anchor_points:
                d = 0.01
                dx = d if pos_x else -d
                dy = d if pos_y else -d
                for (x,y) in anchor_points_for_a_dir:
                    ax1.arrow(x, y, dx, dy, head_width=d/2, head_length=d/2, color='blue')

            colorc = ColorConverter()
            for line in additional_arrows:
                arrow_anchor_x = numpy.float64(line[0][0])
                arrow_anchor_y = numpy.float64(line[0][1])
                arrow_dx = numpy.float64(line[1][0])
                arrow_dy = numpy.float64(line[1][1])
                ax1.arrow(arrow_anchor_x, arrow_anchor_y, arrow_dx, arrow_dy, head_width=0.01, head_length=0.01, color='gray')
            for line in additional_lines:
                point1 = line[0]
                point2 = line[1]
                ax1.plot([point1[0], point2[0]], [point1[1], point2[1]], color='blue')
            for box in additional_boxes_green:
                p = patches.Rectangle((min(box[0][0], box[1][0]),min(box[0][1], box[1][1])), abs(box[0][0] - box[1][0]), abs(box[0][1] - box[1][1]), facecolor=colorc.to_rgba("#4aa02c", 0.6), edgecolor="black", hatch="o")
                ax1.add_patch(p)
            for box in additional_boxes_red:
                p = patches.Rectangle((min(box[0][0], box[1][0]),min(box[0][1], box[1][1])), abs(box[0][0] - box[1][0]), abs(box[0][1] - box[1][1]), facecolor=colorc.to_rgba("#c11b17", 0.6), edgecolor="black", hatch="x")
                ax1.add_patch(p)
            for box in additional_boxes_blue:
                p = patches.Rectangle((min(box[0][0], box[1][0]),min(box[0][1], box[1][1])), abs(box[0][0] - box[1][0]), abs(box[0][1] - box[1][1]), facecolor=colorc.to_rgba("#1b17c1", 0.6), edgecolor="black", hatch="x")
                ax1.add_patch(p)
            pylab.ylim([0,1])
            pylab.xlim([0,1])
            ax1.set_xlabel(str(parameters[0]))
            ax1.set_ylabel(str(parameters[1]))
            #__toggle_selector.RS = RectangleSelector(ax1, __onselect, drawtype='line')
            #pyplot.connect('key_press_event', __toggle_selector)
            if path_to_save != None:
                pyplot.savefig(path_to_save, format="PDF")
            if display:
                pyplot.show()
            pyplot.close(fig)


    def plot_results_val(self, parameters, result):
        if len(parameters) == 2:

            x = []
            y = []
            z = []
            for (key,val) in result.items():
                x.append(key[0])
                y.append(key[1])
                z.append(val)

            cm = pyplot.get_cmap("RdYlGn")
            col = [cm(float(i)) for i in z]
            pyplot.scatter(x,y,s=30,c=col,marker='o')
            pylab.ylim([0,1])
            pylab.xlim([0,1])
            pyplot.show()

