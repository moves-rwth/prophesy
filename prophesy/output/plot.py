import logging
import tempfile

import matplotlib

matplotlib.use('Agg')  # use for plotting without X-server
from matplotlib import pyplot
from matplotlib import patches
from matplotlib.colors import ColorConverter

from shapely.geometry.linestring import LineString
from shapely.geometry.polygon import Polygon

import numpy as np

from prophesy.data.samples import InstantiationResultFlag
from prophesy.data.hyperrectangle import HyperRectangle
from prophesy.config import configuration

logger = logging.getLogger(__name__)


def plot_samples(samples, parameters, safe_above_threshold, threshold):
    """
    Create pdf file displaying the samples.
    :param samples: List of samples.
    :param parameters: Paramaters.
    :param safe_above_threshold: If true, all values above the threshold are considered
                                 safe (indicated by green color), otherwise they are considered
                                unsafe (red color).
    :param threshold: Threshold for safe/unsafe values.
    :return: Path to pdf file containing the samples plot.
    """
    if not safe_above_threshold:
        Plot.flip_green_red = True

    _, plot_path = tempfile.mkstemp(suffix=".pdf", prefix="sampling_", dir=configuration.get_plots_dir())

    samples_non_defined = [res.instantiation.get_point(parameters) for res in samples.instantiation_results() if
                           res.result == InstantiationResultFlag.NOT_WELLDEFINED]
    samples_green = [res.instantiation.get_point(parameters) for res in samples.instantiation_results() if
                     res.result != InstantiationResultFlag.NOT_WELLDEFINED and res.result >= threshold]
    samples_red = [res.instantiation.get_point(parameters) for res in samples.instantiation_results()
                   if res.result != InstantiationResultFlag.NOT_WELLDEFINED and res.result < threshold]

    Plot.plot_results(parameters=parameters, samples_green=samples_green, samples_red=samples_red,
                      samples_black=samples_non_defined,
                      path_to_save=plot_path, display=False)
    logger.info("Samples rendered to {}".format(plot_path))

    return plot_path


class Plot:
    """
    Class handling plotting of samples and result boxes.
    """

    flip_green_red = False

    @staticmethod
    def plot_poly(subplot, poly, *args, **kwargs):
        """
        Plot a polygon or hyperrectangle.
        :param subplot:
        :param poly: Polygon.
        :param args:
        :param kwargs:
        """
        if isinstance(poly, HyperRectangle):
            verts = np.array([np.array(list(map(float, v))) for v in poly.vertices()])
            tmp = np.array(verts[3])
            verts[3] = verts[2]
            verts[2] = tmp
            p = patches.Polygon(verts, *args, **kwargs)

            subplot.add_patch(p)
            return

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
                     samples_green=[], samples_red=[], samples_blue=[], samples_black=[],
                     poly_green=[], poly_red=[], poly_blue_crossed=[], poly_blue_dotted=[], poly_blue=[], poly_black=[],
                     anchor_points=[], additional_arrows=[],
                     path_to_save=None, display=False):
        """
        Plot all results.
        :param parameters: Parameters.
        :param samples_green: Samples with color green.
        :param samples_red: Samples with color red.
        :param samples_blue: Samples with color blue.
        :param poly_green: Polygons with color green.
        :param poly_red: Polygons with color red.
        :param poly_blue_crossed: Polygons with color blue and crossed hatch.
        :param poly_blue_dotted: Polygons with color blue and dotted hatch.
        :param poly_blue: Polygons with color blue.
        :param anchor_points: List of anchor points with direction.
        :param additional_arrows: List of additional arrows.
        :param path_to_save: Paths for pdf file or None if no file should be generated.
        :param display: If true, the plot will be displayed automatically.
        """
        logger.info("Plot results")

        if len(parameters) > 2:
            raise ValueError("Cannot plot for more than 2 parameters.")

        if Plot.flip_green_red:
            samples_green, samples_red = samples_red, samples_green
            poly_green, poly_red = poly_red, poly_green

        if len(parameters) == 1:
            fig = pyplot.figure()
            ax1 = fig.add_subplot(111)
            ax1.plot(samples_green, len(samples_green) * [1], "o", c='green')
            ax1.plot(samples_red, len(samples_red) * [1], "x", c='red')
            ax1.plot(samples_blue, len(samples_blue) * [1], ".", c='blue')
            ax1.plot(samples_black, len(samples_black) * [1], "+", c='black')

            ax1.axes.get_yaxis().set_visible(False)
            ax1.set_xlabel(str(parameters[0].variable))
            ax1.patch.set_visible(False)
            fig.patch.set_visible(False)

            # get rid of the frame
            for spine in fig.gca().spines.values():
                spine.set_visible(False)

            if path_to_save is not None:
                pyplot.savefig(path_to_save, format="PDF")
            if display:
                pyplot.show()
            pyplot.close(fig)

        elif len(parameters) == 2:

            fig = pyplot.figure()
            ax1 = fig.add_subplot(111)

            for anchor in anchor_points:
                d = 0.02
                dx = d if anchor.dir.value[0] else -d
                dy = d if anchor.dir.value[1] else -d
                ax1.arrow(anchor.pos.x, anchor.pos.y, dx, dy, head_width=d / 2, head_length=d / 2, color='blue')

            colorc = ColorConverter()
            for line in additional_arrows:
                line_points = list(line.coords)
                point1 = line_points[0]
                point2 = line_points[1]
                ax1.arrow(point1[0], point1[1], point2[0] - point1[0], point2[1] - point1[1], head_width=0.01,
                          head_length=0.01, color='gray')

            for box in poly_green:
                Plot.plot_poly(ax1, box, fc=colorc.to_rgba("#4aa02c", 0.6), ec=colorc.to_rgba("#4aa02c"), hatch="o")
            for box in poly_red:
                Plot.plot_poly(ax1, box, fc=colorc.to_rgba("#c11b17", 0.6), ec=colorc.to_rgba("#c11b17"), hatch="x")
            for box in poly_blue:
                Plot.plot_poly(ax1, box, fc=colorc.to_rgba("#1b17c1", 0.6), ec=colorc.to_rgba("#1b17c1"))
            for box in poly_black:
                Plot.plot_poly(ax1, box, fc=colorc.to_rgba("#030303", 0.6), ec=colorc.to_rgba("#030303"), hatch="+")
            for box in poly_blue_crossed:
                Plot.plot_poly(ax1, box, fc=colorc.to_rgba("#1b17c1", 0.6), ec=colorc.to_rgba("#1b17c1"), hatch="x")
            for box in poly_blue_dotted:
                Plot.plot_poly(ax1, box, fc=colorc.to_rgba("#1b17c1", 0.6), ec=colorc.to_rgba("#1b17c1"), hatch="o")

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

            x_coords = [x for x, y in samples_black]
            y_coords = [y for x, y in samples_black]
            ax1.scatter(x_coords, y_coords, marker='+', c='black')

            ax1.set_xlim([float(parameters[0].interval.left_bound()), float(parameters[0].interval.right_bound())])
            ax1.set_ylim([float(parameters[1].interval.left_bound()), float(parameters[1].interval.right_bound())])
            ax1.set_xlabel(str(parameters[0].variable))
            ax1.set_ylabel(str(parameters[1].variable))
            if path_to_save is not None:
                pyplot.savefig(path_to_save, format="PDF")
            if display:
                pyplot.show()
            pyplot.close(fig)
