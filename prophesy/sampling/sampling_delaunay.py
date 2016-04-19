import numpy
from prophesy.sampling.sample_generator import SampleGenerator
from prophesy.sampling.voronoi import computeDelaunayTriangulation
from shapely.geometry.point import Point
from shapely.geometry.linestring import LineString
from prophesy import config
from prophesy.data.samples import Sample, weighed_interpolation
from pycarl import Rational

class DelaunayRefinement(SampleGenerator):
    def __init__(self, sampler, intervals, samples, threshold, distance=config.DISTANCE):
        super().__init__(sampler, intervals)
        self.points = self._make_points(samples)
        self.threshold = threshold
        self.distance = distance

    def _make_points(self, samples):
        return [Point(x, y, v) for (x,y), v in samples.items()]

    def __iter__(self):
        # Nothing to prime
        return self

    def __next__(self):
        # Calculate Delaunay triangles and update pointlist
        (self.points, triangles) = self._calc_triangles()
        if len(triangles) == 0:
            raise StopIteration()
        
        # Determine line points
        lines = self._calc_lines(triangles)

        points = []
        for p1, p2 in lines:
            points.append(p1.coords[0])
            line = LineString([p1, p2])
            for d in numpy.arange(0, line.length, self.distance):
                pt = line.interpolate(d)
                points.append(pt.coords[0])
            if p2.distance(Point(points[-1])) > 0.01 and not p2.coords[0] in points:
                # Add final point if not too close to intermediate point
                points.append(p2.coords[0])
        new_samples = self.sampler.perform_sampling(points)
        new_points = self._make_points(new_samples)
        self.points += new_points
        
        filter_points = []
        for i1 in range(0, len(self.points)):
            for i2 in range(i1 + 1, len(self.points)):
                if self.points[i1].distance(self.points[i2]) < 0.001:
                    break
            else:
                filter_points.append(self.points[i1])
        self.points = filter_points

        return new_samples

    def _calc_triangles(self):
        """perform Delaunay triangulation of sample points. Limit the resulting triangles to those
        that contain both a safe and bad point"""
        dtriangles = computeDelaunayTriangulation(self.points)

        triangles = []
        points = set([])
        for triangle in dtriangles:
            points |= set(triangle)
            triangle = [self.points[i] for i in triangle]
            if all([p.z >= self.threshold for p in triangle]):
                continue
            if all([p.z < self.threshold for p in triangle]):
                continue

            # Triangle contains mixture of safe and bad points
            triangles.append(triangle)
        points = [self.points[i] for i in points]

        return points, triangles

    def _calc_lines(self, triangles):
        """Given set of triangle points, return the set of points
        that lie on an edge connecting a safe and bad point. The location
        is weighted by the value of the end points of each line"""
        lines = []
        safe_points = [pt for pt in self.points if pt.z >= self.threshold]
        nsaf = len(safe_points)
        nbad = len(self.points) - nsaf
        if nsaf < nbad:
            # Move towards larger value of more safe samples required
            fudge = 0.01
        else:
            fudge = -0.01

        for triangle in triangles:
            line = []
            points = triangle + [triangle[0]]
            pairs = zip(points[:-1], points[1:])
            for p1, p2 in pairs:
                if (p1.z >= self.threshold) == (p2.z >= self.threshold):
                    continue
                if p1.distance(p2) < 0.001:
                    continue

                sample1 = Sample((Rational(p1.x), Rational(p1.y)), Rational(p1.z))
                sample2 = Sample((Rational(p2.x), Rational(p2.y)), Rational(p2.z))

                midpoint = weighed_interpolation(sample1, sample2, self.threshold, fudge)
                if midpoint is not None:
                    line.append(midpoint)
            # NOTE: A triangle can only have exactly two such points, or none
            # The resulting connecting line thus never splits
            #assert len(line) in [0,2]
            if len(line) == 2:
                lines.append(line)
        return lines
