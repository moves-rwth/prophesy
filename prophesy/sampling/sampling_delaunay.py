import numpy
from prophesy.sampling.sample_generator import SampleGenerator
from prophesy.sampling.voronoi import computeDelaunayTriangulation
from shapely.geometry.linestring import LineString
from prophesy.data.samples import InstantiationResult, weighed_interpolation, SamplePoints
from prophesy.adapter.pycarl import Rational
from prophesy.data.point import Point

class DelaunayRefinement(SampleGenerator):
    def __init__(self, sampler, variables, samples, threshold):
        super().__init__(sampler, variables, samples)
        assert len(variables) == 2, "DelaunayRefinement only works for the 2D case"
        self.points = [Point(x, y, val) for (x, y), val in samples.items()]
        self.threshold = threshold

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
            points.append(p1)
            line = LineString([p1, p2])
            for d in numpy.arange(0, line.length, self.distance):
                shapely_pt = line.interpolate(d)
                pt = Point(Rational(shapely_pt.x), Rational(shapely_pt.y))
                points.append(pt)
            if p2.distance(points[-1]) > 0.01 and not p2 in points:
                # Add final point if not too close to intermediate point
                points.append(p2)
        new_samples = self.sampler.perform_sampling(SamplePoints(points, self.variables))
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

                sample1 = InstantiationResult(Point(Rational(p1.x), Rational(p1.y)), Rational(p1.z))
                sample2 = InstantiationResult(Point(Rational(p2.x), Rational(p2.y)), Rational(p2.z))

                midpoint = weighed_interpolation(sample1, sample2, self.threshold, fudge)
                if midpoint is not None:
                    line.append(midpoint)
            # NOTE: A triangle can only have exactly two such points, or none
            # The resulting connecting line thus never splits
            #assert len(line) in [0,2]
            if len(line) == 2:
                lines.append(line)
        return lines
