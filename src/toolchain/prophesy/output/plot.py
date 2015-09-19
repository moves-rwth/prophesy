import matplotlib
matplotlib.use('Agg') # use for plotting without X-server
from matplotlib import pyplot
from matplotlib import patches
from matplotlib.colors import ColorConverter
from shapely.geometry.linestring import LineString
from shapely.geometry.polygon import Polygon


class Plot(object):
    flip_green_red = False

    @staticmethod
    def plot_poly(subplot, poly, *args, **kwargs):
        if isinstance(poly, Polygon):
            poly = poly.exterior
            
        # If hatched, set edge to black regardless of given argument
        if poly.__class__ != LineString and 'hatch' in kwargs:
            kwargs['ec'] = 'none'

        p = patches.Polygon(poly.coords, *args, **kwargs)
        subplot.add_patch(p)

        # If hatched, set edge to black regardless of given argument
        if poly.__class__ != LineString and 'hatch' in kwargs:
            kwargs['ec'] = 'black'
            kwargs['fill'] = False
            p = patches.Polygon(poly.coords, *args, **kwargs)
            subplot.add_patch(p)

    @staticmethod
    def plot_results(parameters,
                     samples_green=[], samples_red=[], samples_blue=[],
                     poly_green=[], poly_red=[], poly_blue=[],
                     anchor_points=[], additional_arrows=[],
                     path_to_save=None, display=False):
        if len(parameters) == 2:
            if Plot.flip_green_red:
                samples_green, samples_red = samples_red, samples_green
                poly_green, poly_red = poly_red, poly_green

            fig = pyplot.figure()
            ax1 = fig.add_subplot(111)

            for anchor in anchor_points:
                d = 0.02
                dx = d if anchor.dir.value[0] else -d
                dy = d if anchor.dir.value[1] else -d
                ax1.arrow(anchor.pos.x, anchor.pos.y, dx, dy, head_width=d/2, head_length=d/2, color='blue')

            colorc = ColorConverter()
            for line in additional_arrows:
                line_points = list(line.coords)
                point1 = line_points[0]
                point2 = line_points[1]
                ax1.arrow(point1[0], point1[1], point2[0] - point1[0], point2[1] - point1[1], head_width=0.01, head_length=0.01, color='gray')

            for box in poly_green:
                Plot.plot_poly(ax1, box, fc=colorc.to_rgba("#4aa02c", 0.6), ec=colorc.to_rgba("#4aa02c"), hatch="o")
            for box in poly_red:
                Plot.plot_poly(ax1, box, fc=colorc.to_rgba("#c11b17", 0.6), ec=colorc.to_rgba("#c11b17"), hatch="x")
            for box in poly_blue:
                Plot.plot_poly(ax1, box, fc=colorc.to_rgba("#1b17c1", 0.6), ec=colorc.to_rgba("#1b17c1"), hatch=".")

            # Draw the samples last
            x_coords = [x for x, y in samples_green]
            y_coords = [y for x, y in samples_green]
            ax1.scatter(x_coords, y_coords, marker='o', c='green')

            x_coords = [x for x, y in samples_red]
            y_coords = [y for x, y in samples_red]
            ax1.scatter(x_coords, y_coords, marker='x', c='red')

            x_coords = [x for x, y in samples_blue]
            y_coords = [y for x, y in samples_blue]
            ax1.scatter(x_coords, y_coords, marker='.', c='blue')

            ax1.set_ylim([0, 1])
            ax1.set_xlim([0, 1])
            ax1.set_xlabel(str(parameters[0]))
            ax1.set_ylabel(str(parameters[1]))
            if path_to_save is not None:
                pyplot.savefig(path_to_save, format="PDF")
            if display:
                pyplot.show()
            pyplot.close(fig)

        else:
            assert False
