#!/usr/local/bin/python3
import argparse
import sys
import numpy as np
import matplotlib.pyplot as plt
import string
import functools

# global variables
xMin = 1.0 #global x Minimum
xMax = 0.0 #global x Maximum
yMin = 1.0 #global y Minimum
yMax = 0.0 #global y Maximum
addPoint = () #upper right cornerpoint of hull
addMinPoint = () #lower left cornerpoint of hull
subPoint = () #upper left cornerpoint of hull
subMaxPoint = () #lower right cornerpoint of hull

# Graham Scan
TURN_LEFT, TURN_RIGHT, TURN_NONE = (1, -1, 0)

def turn(p, q, r):
	tmp = (q[0] - p[0])*(r[1] - p[1]) - (r[0] - p[0])*(q[1] - p[1])
	return  TURN_LEFT if tmp < 0 else (TURN_NONE if tmp == 0 else TURN_RIGHT)

def _keep_left(hull, r):
	while len(hull) > 1 and turn(hull[-2], hull[-1], r) != TURN_LEFT:
		hull.pop()
	if not len(hull) or hull[-1] != r:
		hull.append(r)
	return hull

def convex_hull(points):
	points = sorted(points)
	l = functools.reduce(_keep_left, points, [])
	u = functools.reduce(_keep_left, reversed(points), [])
	return l.extend(u[i] for i in range(1, len(u) - 1)) or l

def getConstraint(a, b, parameters):
	out = ''
	if(a[0] == b[0]):
		out = (parameters[0] + ' = ' + "{:.9f}".format(a[0]))
		return out
	if(a[1] == b[1]):
		out = (parameters[1] + ' = ' + "{:.9f}".format(a[1]))
		return out
	asc = a[1] - b[1] / a[0] - b[0]
	m = a[1] - asc*a[0]
	out = "{:.9f}".format(asc) +' * ' + parameters[0] + ' - ' + parameters[1] +  ' > -' + "{:.9f}".format(m)
	return out

def sweepline(hull):
	global addPoint
	global addMinPoint
	global subPoint
	global subMaxPoint
	global parameters
	constraints = []
	out = ''
	# get x limitations, which are unequal to 0 or 1
	hull = sorted(hull, key=lambda hull: hull[0])
	if(hull[0][0] != xMin):
		print(parameters[0], ">", hull[0][0])
		out = parameters[0] +  " > " + "{:.9f}".format(hull[0][0])
		constraints.append(out)
		
	if(hull[len(hull)-1][0] != xMax):
		print(parameters[0],"<", hull[len(hull)-1][0])
		out = parameters[0] + " < " + "{:.9f}".format(hull[len(hull)-1][0])
		constraints.append(out)
	# get y limitations, which are unequal to 0 or 1
	hull = sorted(hull, key=lambda hull: hull[1])
	if(hull[0][1] != yMin):
		print(parameters[1], ">", hull[0][1])
		out = parameters[1] + " > " + "{:.9f}".format(hull[0][1])
		constraints.append(out)
	if(hull[len(hull)-1][1] != yMax):
		print(parameters[1], "<", hull[len(hull)-1][1])
		out = parameters[1]+ " < "+ "{:.9f}".format(hull[len(hull)-1][1])
		constraints.append(out)
	# get diagonal constraints
	addedMaximalCoordinates = 0.0
	addedMinimalCoordinates = 2.0
	addedMaximalPoint = []
	addedMinimalPoint = []
	subtractedMinimalCoordinates = 2.0
	subtractedMaximalCoordinates = 0.0
	subtractedMinimalPoint = []
	subtractedMaximalPoint = []
	for point in hull:
		if addedMaximalCoordinates < point[0] + point[1]:
			addedMaximalCoordinates = point[0] + point[1]
			addedMaximalPoint = point
		if addedMinimalCoordinates > point[0] + point[1]:
			addedMinimalCoordinates = point[0] + point[1]
			addedMinimalPoint = point
		if subtractedMinimalCoordinates > point[0] - point[1]:
			subtractedMinimalCoordinates = point[0] - point[1]
			subtractedMinimalPoint = point
		if subtractedMaximalCoordinates < point[0] - point[1]:
			subtractedMaximalCoordinates = point[0] - point[1]
			subtractedMaximalPoint = point
	if addedMaximalPoint:
		print(parameters[0],"+", parameters[1],"-", (addedMaximalPoint[1]-addedMaximalPoint[0]),"< 0")
		out = parameters[0] + " + " + parameters[1] + " - " + "{:.9f}".format(addedMaximalPoint[1]-addedMaximalPoint[0]) + " < 0"
		constraints.append(out)
		addPoint = addedMaximalPoint
	if subtractedMinimalPoint:
		print("-",parameters[0],"+",parameters[1],"-", (subtractedMinimalPoint[1]-subtractedMinimalPoint[0]),"< 0")
		out = "-"+parameters[0] + " + " + parameters[1] + " - " + "{:.9f}".format(subtractedMinimalPoint[1]-subtractedMinimalPoint[0]) + " < 0"
		constraints.append(out)
		subPoint = subtractedMinimalPoint
	if addedMinimalPoint:
		print(parameters[0],"+",parameters[1],"-",(addedMinimalPoint[1]-addedMinimalPoint[0]),"> 0")
		out = parameters[0] + " + " + parameters[1] + " - " + "{:.9f}".format(addedMinimalPoint[1]-addedMinimalPoint[0]) + " > 0"
		constraints.append(out)
		addMinPoint = addedMinimalPoint
	if subtractedMaximalPoint:
		print("-",parameters[0],"+",parameters[1],"-",(subtractedMaximalPoint[1]-subtractedMaximalPoint[0]),"> 0")
		out = "-" + parameters[0] + " + " + parameters[1] + " - " + "{:.9f}".format(subtractedMaximalPoint[1]-subtractedMaximalPoint[0]) + " > 0"
		constraints.append(out)
		subMaxPoint = subtractedMaximalPoint
	write_constraints(constraints, vars(commandlineArgs)['out'])



def getConstraintsSweepline(hull, threshold):
	lessHull = set()
	greaterHull = set()
	for point in hull:
		if(point[2] < threshold):
			lessHull.add(point)
		else:
			greaterHull.add(point)
	if lessHull:
		print("Sweepline lessHull:")
		sweepline(lessHull)
	if greaterHull:
		print("Sweepline greaterHull:")
		sweepline(greaterHull)


# output functionality
def print_cloud(points, color):
	xCoordinates = []
	yCoordinates = []
	for point in points:
		xCoordinates.append(point[0])
		yCoordinates.append(point[1])
	plt.plot(xCoordinates, yCoordinates, color)
	plt.axis([0,1,0,1])
	plt.show()

def print_hull(points, hull):
	xCoordinates = []
	yCoordinates = []
	for point in points:
		xCoordinates.append(point[0])
		yCoordinates.append(point[1])
	plt.plot(xCoordinates, yCoordinates, 'ro')
	xCoordinates = []
	yCoordinates = []
	for point in hull:
		xCoordinates.append(point[0])
		yCoordinates.append(point[1])
	plt.plot(xCoordinates, yCoordinates, 'bo')

	# print optional subPoint and addPoint
	print(addPoint, subPoint, subMaxPoint, addMinPoint)
	if subPoint != ():
		plt.plot(subPoint[0], subPoint[1], 'go')
	if addPoint != ():
		plt.plot(addPoint[0], addPoint[1], 'go')
	if subMaxPoint != ():
		plt.plot(subMaxPoint[0], subMaxPoint[1], 'go')
	if addMinPoint != ():
		plt.plot(addMinPoint[0], addMinPoint[1], 'go')

	plt.axis([0,1,0,1])
	plt.show()

def print_constraints(hull, parameters):
	stringSet = []
	for i in range(len(hull)-1):
		stringSet.append(getConstraint(hull[i], hull[i+1], parameters))
		print(getConstraint(hull[i], hull[i+1], parameters))
	print(getConstraint(hull[len(hull)-1], hull[0], parameters))
	stringSet.append(getConstraint(hull[len(hull)-1], hull[0], parameters))
	return stringSet

def write_constraints(constraints, file):
	fileobj = open(file, 'w')
	for constraint in constraints:
		fileobj.write(constraint)
		fileobj.write('\n')
	fileobj.close()

# input parser
parser = argparse.ArgumentParser(description='Create a reduced constraint set out of a pointcloud.')
parser.add_argument('--file', help='input file containing the pointcloud', required=True)
parser.add_argument('--constraints', type=int, help='maximal number of constraints created')
parser.add_argument('--out', help='Specified output file', default='out')
commandlineArgs = parser.parse_args()

points = set()
threshold = 0.0
parameters = []
inputfile = open(vars(commandlineArgs)['file'])

#parse the input file until the beginning of the samples
line = inputfile.readline()
while not '## SAMPLES' in line:
	if '## PARAMETERS:' in line:
		
		parameters = inputfile.readline().split()
	if ('## THRESHOLD:') in line:
		threshold = float(inputfile.readline())
		print('Threshold = %f' %threshold)
	line = inputfile.readline()

line = inputfile.readline()
while line != '':
	#print(line)
	tmpPoint = ((float(line.split()[0]), float(line.split()[1]), float(line.split()[2])))
	if xMin > tmpPoint[0]:
		xMin = tmpPoint[0]
	elif xMax < tmpPoint[0]:
		xMax = tmpPoint[0]
	if yMin > tmpPoint[1]:
		yMin = tmpPoint[1]
	elif yMax < tmpPoint[1]:
		yMax = tmpPoint[1]
	points.add(tmpPoint)
	
	line = inputfile.readline()
inputfile.close()

#find only neccessary points
reducedPoints = set()
for point in points:
	if(point[2] < threshold):
		reducedPoints.add(point)
#print('Added Point ', point)

#print_cloud(reducedPoints, 'ro')
#compute the convex hull
hull = convex_hull(reducedPoints)

#write_constraints(print_constraints(hull, parameters), vars(commandlineArgs)['out'])

getConstraintsSweepline(hull, 0.6)
print_cloud(reducedPoints, ".r")
print_hull(reducedPoints, hull)