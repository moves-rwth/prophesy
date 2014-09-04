#!/env/python3
import sys
import os
# import library. Using this instead of appends prevents naming clashes..
thisfilepath =  os.path.dirname(os.path.realpath(__file__))
sys.path.insert(0, os.path.join(thisfilepath, '../lib'))

import bottle
from bottle import request, route, hook, static_file
import beaker.middleware
import json

import argparse
import math
import config
from checks import *
from data.constraint import Constraint
from data.rationalfunction import RationalFunction
from sympy.polys import Poly
import iterable_param
from input.comics import *
from input.additional_constraints import *
from output.output import *
from output.smt2 import *
from output.plot import *
from output.samplepoints import *



RESULTFILES_DIR = os.path.join(INTERMEDIATE_FILES_DIR, "results/")



@hook('before_request')
def setup_request():
    request.session = request.environ['beaker.session']
    if 'threshold' not in request.session: 
        request.session['threshold'] = 0.3

@route('/ui/<filepath:path>')
def server_static(filepath):
    return static_file(filepath, root=WEB_INTERFACE_DIR)

@route('/')
def index():
    if 'something' in request.session:
       request.session['something'] = request.session['something'] + 1
       return str(request.session['something'])

    request.session['something'] = 0

@route('/uploadComicsResult/', method='POST')    
def uploadComicsResult():
    upload     = bottle.request.files.get('upload')
    name, ext = os.path.splitext(upload.filename)
#    if ext not in ('.png','.jpg','.jpeg'):
#        return 'File extension not allowed.'

#    save_path = get_save_path_for_category(category)
    save_path = os.path.join(RESULTFILES_DIR, upload.filename)
    inputfile = open(save_path, 'wb')
    inputfile.write(upload.file.read())
    inputfile.close()
    return 'OK'

    return str("Success")

@route('/listAvailableResultFiles/')
def loadAvailableResults():
    files = [f for f in os.listdir(RESULTFILES_DIR) if f.endswith('.pol')]
    files.sort()
    return json.dumps(files)
    
@route('/loadComicsResult/<filename>')    
def loadComicsResult(filename):    
    filepath = os.path.join(RESULTFILES_DIR, filename)
    [parameters, constraints, nominator, denominator] = get_polynomials_from_comics_file(filepath)
    
    request.session['constraints'] = constraints
    request.session['parameters'] = parameters
    request.session['ratfunc'] = RationalFunction(nominator, denominator)
    print(str(request.session['ratfunc']))
    return json.dumps([str(request.session['ratfunc'])])

@route('/setThreshold/<threshold:float>')
def setThreshold(threshold):
    request.session['threshold'] = threshold

@route('/showRationalFunction/')
def showRationalFunction():
    if 'ratfunc' in request.session:
       return json.dumps([str(request.session['ratfunc'])])
   
@route('/manualCheckSamples/', method="POST")
def manualCheckSamples():
    spots = bottle.request.json
    print(spots)
    if 'ratfunc' not in request.session:
        return 'fail'
    if 'parameters' not in request.session:
        return 'fail'
    ratfunc = request.session['ratfunc']
    parameters = request.session['parameters']
    samples = request.session['samples']
    for spot in spots:
        value = ratfunc.evaluate(zip(parameters, [float(x) for x in spot]))
        point = tuple([float(x) for x in spot])
        samples[point] = value    
    request.session['samples'] = samples
    
    return json.dumps('ok')
    
    
   
@route('/calculateSamples/<iterations:int>/<nrsamples:int>')
def calculateSamples(iterations, nrsamples):
    
    if 'ratfunc' not in request.session:
        return 'fail'
    if 'parameters' not in request.session:
        return 'fail'
    ratfunc = request.session['ratfunc']
    print(ratfunc)
    parameters = request.session['parameters']
    print(parameters)
    threshold = request.session['threshold']
    samples = {}
       
    i = 0
    bd = 0.1
    while(i < iterations):
        print("iteration {0} / {1}".format(i+1, iterations))
        if len(samples) == 0: 
            #evaluate rational function at specific points    
            for p in iterable_param.IterableParam(parameters,nrsamples, bound_distance=bd):
                evalVal = ratfunc.evaluate(p)
                point = tuple([value for [variable, value] in p])
                print(point)
                samples[point] = evalVal
        epsilon = (1-2*bd)/(nrsamples-1)
        delta = math.sqrt(2*(epsilon*epsilon) + epsilon/2)
        j = 0
        while j < 2:
            good_samples = [k for k,v in samples.items() if v > threshold]
            bad_samples = [k for k,v in samples.items() if v <= threshold]
            for gs in good_samples:
                for bs in bad_samples:
                    distance = math.hypot(gs[0]-bs[0], gs[1]-bs[1])
                    #print(str(gs) + " -- " + str(bs) + ": " + str(distance))   
                    if distance < delta:
                        p = tuple([(i_gs + i_bs)/2 for i_gs, i_bs in zip(gs,bs)])
                        samples[p] = ratfunc.evaluate(zip(parameters, p))
            j = j + 1
            delta = delta * 0.7
        i = i + 1    
        #print(samples)    
        # display
        #if vars(cmdargs)['display'] == 'val' or  vars(cmdargs)['display'] == 'all':
            #plot_results_val(parameters, samples)        
        #if vars(cmdargs)['display'] == 'bool' or  vars(cmdargs)['display'] == 'all':
            #plot_results_bool(parameters, dict([(p, v > threshold) for p,v in samples.items()])) 
    request.session['samples'] = samples
    flattenedsamples = list([{"coordinates" : [str(c) for c in k], "value" : str(v)} for k, v in samples.items()])
    print(flattenedsamples)
    return json.dumps(flattenedsamples)

@route('/getSamples/')
def getSamples():
    flattenedsamples = list([{"coordinates" : [str(c) for c in k], "value" : str(v)} for k, v in request.session['samples'].items()])
    return json.dumps(flattenedsamples)
    
    
if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Start a webservice for ' + TOOLNAME)
    parser.add_argument('--server-port',  type=int, help='the port the server listens on', default=4242)
    parser.add_argument('--server-host',  help="server host name", default="localhost")
    parser.add_argument('--server-debug', type=bool, help='run the server in debug mode', default=True)
    parser.add_argument('--server-quiet', type=bool, help='run the server in quiet mode', default=False)
    cmdargs = parser.parse_args()    
    
    ensure_dir_exists(INTERMEDIATE_FILES_DIR)
    ensure_dir_exists(RESULTFILES_DIR)

    session_opts = {
        'session.type': 'file',
        'session.data_dir': WEBSESSIONS_DIR,
        'session.auto': True,
    }

    app = beaker.middleware.SessionMiddleware(bottle.app(), session_opts)
    bottle.run(app=app,host=vars(cmdargs)['server_host'], port=vars(cmdargs)['server_port'], debug=vars(cmdargs)['server_debug'], quiet=vars(cmdargs)['server_quiet'])
