#!/usr/bin/python3
# encoding: utf8

# CaspR - Semi-Automatic Coreference Resolution Adjudication Tool based on Answer Set Programming
# Copyright (C) 2015-2017 Peter Schüller <schueller.p@gmail.com>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

import sys
import re
import collections
import itertools
import os
import shutil
import subprocess
import json
import argparse
import threading
import pexpect
import time

# TODO detect clingo/search for clingo/check if version is ok (needs to support USC optimization mode)
CLINGO = 'clingo-5.2.0'
# accept suboptimal solutions if optimum not proved after so many seconds (set to None for infinite)
TIMELIMIT = 900
PREFIX = 'CaspR: '
# either 'table' or 'tabs', human readable = table
OUTPUTMETHOD = 'table'

config = {}

def warn(s):
  sys.stderr.write(PREFIX+s+'\n')

def interpretArguments(argv):
  global config
  parser = argparse.ArgumentParser(
    description='CaspR - Semi-Automatic Coreference Resolution '
      'Adjudication Tool based on Answer Set Programming')
  parser.add_argument('--ann', nargs='+', required=True, metavar='IN', action='append',
    help='CoNLL-format input file with coreference annotation in last column. These annotations will be merged.')
  parser.add_argument('--obj', required=True, default='v',
    help='Objective function to minimize (default=v): '
      'v  performs voting for mention-mention linkes (existing vs missing annotations),'
      'va is like v but additionally allows non-annotated transitive links with cost 1,'
      'u  aims to use as many mention-mention links as possible (even if minority of annotators annotated it),'
      'ua is like u but additionally allows non-annotated transitive links with cost 1.')
  parser.add_argument('--representation', nargs='?', action='store', metavar='REP', default='mm',
    help='Use representation {mm,cm} (default=mm).')
  parser.add_argument('--out', nargs='?', action='store', metavar='OUT',
    help='Automatic adjudication: store CoNLL-format to OUT file.')
  parser.add_argument('--redo', nargs='?', action='store', metavar='INOUT',
    help='Semi-automatic adjudication: read manually forced token annotations from INOUT file '
      'and store result to INOUT (creates backup files).')
  parser.add_argument('--factout', nargs='?', action='store', metavar='FACTOUT',
    help='Store ASP facts to FACTOUT file.')
  parser.add_argument('--aspout', nargs='?', action='store', metavar='ASPOUT',
    help='Store ASP program to ASPOUT file.')
  parser.add_argument('--nocomp', action='store_true', default=False, help='Do not call solver')
  parser.add_argument('--anonymize', action='store_true', default=False, help='Remove comments and filenames')
  parser.add_argument('--all', action='store_true', default=False, help='Output all solutions with number postfixes.')
  parser.add_argument('--tabformat', action='store_true', default=False, help='Output in tabbed format (default = space)')
  parser.add_argument('--debug', action='store_true', default=False,
    help='Show output of solver on stderr.')
  parser.add_argument('--tool', nargs='?', action='store', metavar='TOOL',
    help='Use TOOL commandline to call grounder+solver (parse ASP-Core-2). Must contain either "wasp" or "clasp".')
  parser.add_argument('--timeout', nargs='?', action='store', metavar='TIME',
    help='Limit the optimization to TIME seconds (use suboptimal results).')
  args = parser.parse_args(argv)
  #warn('args='+repr(args))

  # configure input annotations
  annotations = []
  #warn('args.ann='+repr(args.ann))
  for annlist in args.ann:
    for ann in annlist:
      # XXX interpret input column specifiers from commandline
      cols = 'last'
      if len(annotations) == 0:
        cols = 'all'
      annotations.append({'path':ann, 'columns':cols, 'corefcolumn':'last'})

  # out/inout file
  if args.out and args.redo:
    parser.print_help()
    raise Exception("Cannot have --out and --redo together!")
  if not args.out and not args.redo:
    parser.print_help()
    raise Exception("Need either --out or --redo argument!")
  if args.out:
    inout = args.out
    mode = 'auto'
  else:
    inout = args.redo
    mode = 'redo'

  config['representation'] = args.representation
  config['aspout'] = args.aspout
  config['factout'] = args.factout
  config['nocomp'] = args.nocomp
  config['anonymize'] = args.anonymize
  config['debug'] = args.debug
  config['all'] = args.all
  config['timelimit'] = TIMELIMIT

  if args.tabformat:
    configureOutputMethod('tabs')

  if not args.tool:
    detectClingo()
    config['tool'] = CLINGO
    config['tooltype'] = 'clasp'
    # default timelimit if we autodetect the solver (can be overwritten by explicit timeout)
    #config['timelimit'] = 120
  else:
    config['tool'] = args.tool
    if 'clasp' in args.tool or 'clingo' in args.tool:
      config['tooltype'] = 'clasp'
    elif 'wasp' in args.tool:
      config['tooltype'] = 'wasp'
    else:
      raise Exception('Tool "{}" type cannot be detected (must contain clasp, clingo, or wasp in the name'.format(args.tool))

  if args.timeout:
    if int(args.timeout) == 0:
      config['timelimit'] = None
    else:
      config['timelimit'] = int(args.timeout)

  return annotations, inout, mode, args.obj, config

def interpretCoNLLRaw(filename, lines, usecolumns, corefcolumn, onlyUser=False):
  '''
  this is for one document, output in format
    {
      'lines': [ '1\t3\t...\t(2)', '3\t...\t-', ... ],
      'mentions': { id: (linefrom,lineto), ... },
      'chains': { id: set([id1,id2]), ... }
      'none': set([line, ...]),
    }

  filename is only for giving better warning messages!
  '''
  out = { 'lines':[], 'mentions':{}, 'chains':collections.defaultdict(set), 'none': set() }
  ignored_nonempty = 0
  mentionId = 0
  openMentions = [] # (lineidx, chainID) tuples go here
  rCorefAtom = re.compile(r'^(\([0-9]+\)|\([0-9]+|[0-9]+\)).*$')
  maxidx = max(usecolumns)
  for lineidx, line in enumerate(lines):
    if len(line) <= maxidx:
      raise Exception("short line: want to use field {} but found only {} fields in '{}'".format(maxidx+1, len(line), repr(line)))
    thisline = [ line[idx] for idx in usecolumns ]
    out['lines'].append(thisline)
    coref = line[corefcolumn]
    if onlyUser:
      if coref[0] == '=':
        # ignore = and process
        coref = coref[1:]
      else:
        # ignore coref because we only want user annotations
        if coref != '-':
          # count ignored non-empty annotations
          ignored_nonempty += 1
        continue
    while len(coref) > 0 and coref != '-':
      m = rCorefAtom.match(coref)
      if m is None:
        raise Exception("uninterpretable coreference information '{}'".format(coref))
      #warn('m.groups {}'.format(m.groups()))
      match = m.groups()[0]
      # interpret match
      if match[0] == '(' and match[-1] == ')':
        # (XYZ)
        chain = int(match[1:-1])
        out['mentions'][mentionId] = (lineidx, lineidx)
        out['chains'][chain].add(mentionId)
        mentionId += 1
      elif match[0] == '(':
        # (XYZ
        chain = int(match[1:])
        openMentions.append( (lineidx, chain) )
      elif match[-1] == ')':
        # XYZ)
        chain = int(match[:-1])
        if len(openMentions) == 0:
          raise Exception('no open mentions but closing mention for chain {}'.format(chain))
        if openMentions[-1][1] != chain:
          raise Exception('closing mention for chain {} but currently innermost open mention is for chain {}'.format(
            chain, openMentions[-1][1]))
        fromline = openMentions[-1][0]
        out['mentions'][mentionId] = (fromline, lineidx)
        out['chains'][chain].add(mentionId)
        mentionId += 1
        openMentions = openMentions[:-1]
      else:
        raise Exception("unexpected case for match '{}'".format(match))

      # remove this coref element
      coref = coref[len(match):]
    if coref == '-':
      out['none'].add(lineidx)
  if onlyUser and ignored_nonempty > 0:
    warn("ignored {} non-empty non-forced annotations in file {} while interpreting user CoNLL".format(ignored_nonempty, filename))
  rmchains = []
  rmmentions = []
  singlementionchains = 0
  for cid, c in out['chains'].items():
    if len(c) == 1:
      mid = list(c)[0]
      singlementionchains += 1
      if config['debug']:
        warn("in file {} found chain with id {} containing only one mention {}! (ignored)".format(
          filename, cid, repr(out['mentions'][mid])))
      rmchains.append(cid)
      rmmentions.append(mid)
  if singlementionchains > 0:
    warn("ignored {} single-mention chains in file {}".format(singlementionchains, filename))
  for mid in rmmentions:
    del(out['mentions'][mid])
  for c in rmchains:
    del(out['chains'][c])
  return out

def readCONLLRaw(text):
  'output in format { documentname : [ lines ], ... }'
  out = collections.OrderedDict()
  rBeginDoc = re.compile(r'^#\s*begin\s+document\s*\((.*)\)\s*;\s*$')
  rEndDoc = re.compile(r'^#\s*end\s+document\s*$')
  rFieldSplitter = re.compile(r'[\t ]+')
  currentDoc = None
  currentDocLines = []
  for line in text.split('\n'):
    beg = rBeginDoc.findall(line)
    end = rEndDoc.findall(line)
    #warn('beg {}'.format(repr(beg)))
    if len(beg) > 0:
      if currentDoc is not None:
        raise Exception('encountered begin document {} within document {}'.format(beg[0], currentDoc))
      currentDoc = beg[0]
    elif len(end) > 0:
      if currentDoc is None:
        raise Exception('encountered end document outside of document')
      out[currentDoc] = currentDocLines
      currentDoc = None
      currentDocLines = []
    elif line.strip() == '':
      # handle empty lines gracefully
      pass
    else:
      fields = rFieldSplitter.split(line.strip())
      if currentDoc is None:
        raise Exception('encountered data outside of #begin document / #end document')
      currentDocLines.append(fields)
  return out

def readInput(filespec, onlyUser=False):
  filename = filespec['path']
  with open(filename, 'r') as f:
    rawdocs = readCONLLRaw(f.read())
    out = collections.OrderedDict()
    for docname, docdata in rawdocs.items():
      if len(docdata) == 0:
        out[docname] = {}
        continue
      ncolumns = len(docdata[0])
      corefcolumn = ncolumns - 1
      if filespec['columns'] == 'last':
        usecolumns = [ ncolumns-1 ]
      elif filespec['columns'] == 'all':
        usecolumns = [ x for x in range(0,ncolumns) ]
      else:
        usecolumns = [ int(x) for x in filespec['columns'].split(',') ]
      if filespec['corefcolumn'] != 'last':
        corefcolumn = int(filespec['corefcolumn'])
        if corefcolumn not in usecolumns:
          raise Exception('coreference column must be within used columns')
      out[docname] = interpretCoNLLRaw(filename, docdata, usecolumns, corefcolumn, onlyUser)
    return (filename, out)

def findCommonDocuments(annotationdata):
  # extract only doc names in original order
  docnames = [ adic[1].keys() for adic in annotationdata ]
  # save original order
  orderedDocs = docnames[0]
  # map to sets
  docnames = [ set(x) for x in docnames ]
  # build intersection of all sets
  commonDocs = docnames[0]
  for dn in docnames[1:]:
    commonDocs = commonDocs & dn
  # get original order but only those present in all files
  orderedDocs = [x for x in orderedDocs if x in commonDocs ]
  return orderedDocs

#def keepOnlyCommonDocuments(annotationdata, commonDocs):
#  def keepCommon(annotation):
#    filename, docsdict = annotation
#    out = {}
#    for d in commonDocs:
#      out[d] = docsdict[d]
#    return (filename, out)
#  return map(keepCommon, annotationdata)

def consolidateAll(objective, annotations, forcedannotation, config):
  basis = list(annotations) # duplicate
  if forcedannotation:
    basis.append(forcedannotation)
  commonDocs = findCommonDocuments(basis)
  # actually we do not need this because we filter implicitly below
  #annotations = keepOnlyCommonDocuments(annotations, commonDocs)
  #forcedannotations = keepOnlyCommonDocuments(forcedannotations, commonDocs)
  results = collections.OrderedDict()
  for doc in commonDocs:
    def selectDocument(annotation, docname):
      filename, documents = annotation
      return (filename, documents[docname])
    #warn("anno "+repr(annotations))
    #warn("forcedanno "+repr(forcedannotations))
    selected_annotations = [ selectDocument(anno, doc) for anno in annotations ]
    selected_forcedannotation = None
    if forcedannotation:
      selected_forcedannotation = selectDocument(forcedannotation, doc)
    docresults = consolidate(objective, doc, selected_annotations, selected_forcedannotation, config)
    results.update(docresults)
  return results

anonymousfileconst = {}
def createInputFacts(annotations, forcedannotation=None):

  def mentionFacts(fileconst, mentions):
    global config
    out = []
    #warn('mentions '+repr(mentions))
    for mid, mdata in mentions.items():
      mfrom, mto = mdata
      comment = ''
      if not ('anonymize' in config and config['anonymize']):
        comment = '% from {} to {}\n'.format(repr(annodict['lines'][mfrom]), repr(annodict['lines'][mto]))
      out.append(comment + 'mention({},{},{},{}).'.format(fileconst, mid, mfrom, mto))
    return out

  def chainFacts(fileconst, chains):
    out = []
    #warn('chains '+repr(chains))
    for cidx, chain in chains.items():
      #warn('chain {}: {}'.format(cidx, chain))
      for midx in chain:
        #warn('  midx {}'.format(midx))
        out.append('chainmention({},{},{}).'.format(fileconst,cidx, midx))
    return out

  global config
  global anonymousfileconst
  mfacts, cfacts, lfacts = [], [], []
  maxminchain, maxtoken, sumchain, summention = 0, 0, 0, 0
  sannotations = sorted(annotations, key=lambda x: x[0])
  for ann in sannotations:
    #warn('annotation: '+repr(ann))
    filename, annodict = ann
    # TODO escape if " in filename for ASP
    fileconst = '"{}"'.format(filename)
    if 'anonymize' in config and config['anonymize']:
      if fileconst not in anonymousfileconst:
        anonymousfileconst[fileconst] = str(len(anonymousfileconst))
      fileconst = anonymousfileconst[fileconst]

    mfacts += mentionFacts(fileconst, annodict['mentions'])
    cfacts += chainFacts(fileconst, annodict['chains'])
    summention += len(annodict['mentions'])
    sumchain += len(annodict['chains'])
    maxtoken = max(maxtoken, len(annodict['lines']))
    # max number of mentions in chain
    maxminchain = max(maxminchain, max([ len(x) for x in annodict['chains'].values()]))
  for ann in [forcedannotation for x in [1] if forcedannotation]:
    #warn('forced annotation: '+repr(ann))
    unused_filename, annodict = ann
    mfacts += mentionFacts('forced', annodict['mentions'])
    cfacts += chainFacts('forced', annodict['chains'])
    lfacts += [ 'emptyline({}).'.format(lineno) for lineno in annodict['none'] ]
  # number of tokens in doc = same in all docs, just take max
  warn('creating facts: {} tokens, {} annotations, {} mentions, {} chains (longest {} mentions), {} empty lines'.format(
    maxtoken, len(sannotations), summention, sumchain, maxminchain, len(lfacts)))
  return mfacts + cfacts + lfacts

def parseAtom(atmstr):
  '''
  parse an atom into a tuple of arguments
  (parse arbitrarily nested terms as strings)
  '''
  out = []
  openbrackets = 0
  start = None
  for idx, char in enumerate(atmstr):
    if char == '(':
      if not start:
        # we went over the predicate successfully
        start = idx+1
        # record predicate
        out.append(atmstr[:idx])
      else:
        openbrackets += 1
    elif char == ')':
      assert(start)
      openbrackets -= 1
      if openbrackets == -1:
        # record last argument
        out.append(atmstr[start:idx])
        #warn("from '{}' extracted {}".format(atmstr, repr(out)))
        return tuple(out)
    elif char == ',':
      assert(start)
      if openbrackets == 0:
        # record argument in argument list (not last)
        out.append(atmstr[start:idx])
        start = idx+1
  assert(out == [])
  # constant atom without arguments
  #warn("from '{}' extracted []".format(atmstr))
  return ( atmstr, )

def runASP(code, config):
  'run ASP optimization on code and return sequence of answer sets'
  if config['tooltype'] == 'clasp':
    return runASPClasp(code, config)
  else:
    return runASPWasp(code, config)

def runInPExpect(args, code, timelimit, logprefix=None):
  # with subprocess it is much easier:
  #clingop = subprocess.Popen(args, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=sys.stderr)
  #out, err = clingop.communicate(code)
  # BUT we cannot do 'live' watching of the optimization
  # because the solver buffers -> pexpect

  # with pexpect, live watching possible
  # because pexpect runs the child in a terminal
  # so it will buffer per line
  def sender(proc, what):
    #sys.stderr.write('sender started\n')
    proc.send(what)
    #sys.stderr.write('sender after write\n')
    proc.sendcontrol('d')
    #sys.stderr.write('sender after send-ctrl-d\n')
    proc.sendeof()
    #sys.stderr.write('sender after sendeof\n')

  pexp = pexpect.spawn(args[0], args[1:], timeout=None)
  pexp.setecho(False)
  pexp.waitnoecho()
  #sys.stderr.write('after waitnoecho\n')
  tsend = threading.Thread(target=sender, args=[pexp, code])
  tsend.daemon = True
  tsend.start()
  #sys.stderr.write('after start\n')

  def killer(who, delay, signal):
    #sys.stderr.write("killer waiting {}\n".format(delay))
    time.sleep(delay)
    sys.stderr.write("Solving timeout after {} seconds! (using non-optimal result if one exists)\n".format(delay))
    who.kill(signal)
  # 15 = SIGTERM
  tkill = None
  if timelimit:
    tkill = threading.Thread(target=killer, args=[pexp, timelimit, 15])
    tkill.daemon = True
    tkill.start()

  # because of using pexpect we cannot distinguish stdout and stderr!
  # (we can use pexpect on a Popen file descriptor but then clasp will buffer again and we are not able to log the output live!)
  out = []
  line = pexp.readline().decode("utf-8")
  nextout = time.time()
  lastprogression = None
  try:
    while line != '':
      out.append(line)
      if logprefix:
        sys.stderr.write(logprefix+line)
        sys.stderr.flush()
      elif line.startswith('Optimization:'):
        sys.stderr.write(line)
        sys.stderr.flush()
      elif line.startswith('Progression :'):
        lastprogression = line
        if time.time() > nextout:
          nextout = time.time() + 10.0 # output progression only all 10 seconds
          sys.stderr.write(line)
          sys.stderr.flush()
      line = pexp.readline().decode("utf-8") 
  except:
    pexp.kill(15)
    raise
  #sys.stderr.write('after readline loop\n')
  if lastprogression:
    sys.stderr.write(lastprogression+'\n')
  return out

def runASPClasp(code, config):
  args = config['tool'].split(' ')
  #args.extend(['--outf=2']) # json output

  if config['tool'] == CLINGO:
    # for default solver use these settings, for other solvers do not use specific settings (get them in 'tool' variable)
    args.append('--opt-strategy=usc,9') # unsatisfiable core optimization mode (speedup)
    args.append('--stats=2')
    if config['all'] == True:
      args.append('--opt-mode=optN')
      args.append('0')
  out = None
  if config['debug']:
    warn('running {} with timeout {}'.format(' '.join(args), repr(config['timelimit'])))
    out = runInPExpect(args, code, config['timelimit'], '[clasp] ')
  else:
    out = runInPExpect(args, code, config['timelimit'], None)

  ## because of having stdout and stderr together in pexpect, json format is not usable
  #clingoout = json.loads(out)
  #warn('clingo out = '+repr(clingoout))
  #if 'Witnesses' not in clingoout['Call'][0]:
  #  raise Exception('failed obtaining answer sets. '
  #   'if timeout is the problem, try using --approx=50 or --approx=100, if memory is the problem, try additionally using --lowmem\n'
  #   'clingo output:\n'+out)
  #witnesses = clingoout['Call'][0]['Witnesses']
  #solution = witnesses[-1]
  #warn('clingo cost {} res {} stats {}'.format(solution['Costs'], clingoout['Result'], clingoout['Time']))
  #warn('solution = '+repr(solution))
  #atoms = map(parseAtom, solution['Value'])
  #return atoms

  answersets = set([])
  bestcost = None
  optimal = False
  lineiter = iter(out)
  try:
    while True:
      line = next(lineiter)
      if line.startswith('Answer: '):
        answerset = next(lineiter).strip()
        cost = next(lineiter).split(' ',1)[1].strip()
        #warn("got cost "+repr(cost)+" at bestcost "+repr(bestcost)+"with {} answersets".format(len(answersets)))
        if bestcost is None or cost != bestcost:
          bestcost = cost
          answersets = set([])
        answersets.add(answerset)
      elif line.startswith('OPTIMUM FOUND'):
        optimal = True
  except StopIteration:
    pass
  if len(answersets) == 0:
    raise Exception('clingo found no answer set')
  warn('found {} answer sets with cost {} optimal={}'.format(len(answersets), repr(cost), str(optimal)))
  if config['debug']:
    for answerset in answersets:
      warn('Answer Set: '+repr(answerset))
  # we assume that the answer set does not contain atoms that contain spaces within strings
  # (this can be assumed as we show only relevant atoms containing only const/integer terms in output)
  if config['all']:
    return [ map(parseAtom, s.split(' ')) for s in answersets ]
  else:
    # only return last
    return [ map(parseAtom, s.split(' ')) for s in answersets[-1:] ]

def runASPWasp(code, config):
  # TODO WASP code not adapted for multiple answer sets (--all option)
  args = config['tool'].split(' ')
  out = None
  if config['debug']:
    warn('running {} with timeout {}'.format(' '.join(args), repr(config['timelimit'])))
    out = runInPExpect(args, code, config['timelimit'], '[wasp] ')
  else:
    out = runInPExpect(args, code, config['timelimit'], None)

  last = None
  cost = None
  prevline = None
  lineiter = iter(out)
  try:
    while True:
      line = lineiter.next()
      if line.startswith('COST '):
        # XXX this only works with a single cost level
        cost = line.strip().split(' ')[1].split('@')[0]
        last = prevline
      prevline = line
  except StopIteration:
    pass
  if last is None:
    raise Exception('wasp found no answer set')
  last = last.strip()[1:-1]
  warn('wasp: found last answer set with cost {}: {}'.format(repr(cost), repr(last)))
  # TODO code not adapted for multiple answer sets (--all option)
  return [ map(parseAtom, last.split(', ')) ]

##############################################################################
# encodings
##############################################################################
encoding_common = '''
  % common structural constraints
  % require more than one mention in a chain
  :- resultchain(C), #count { Y : resultcm(C,Y) } <= 1.
  % forbid mentions within mentions in same chain
  :- resultcm(C,mid(From1,To1)), resultcm(C,mid(From2,To2)),
     From1 <= From2, To2 <= To1, (From1,To1) != (From2,To2).
  % Number of files and mentions vs canonical mentions.
  numfiles(NF) :- NF = #count { F : mention(F,_,_,_) }.
  cfmention(F,M,mid(From,To)) :- mention(F,M,From,To).

  % Which noncanonical and canonical mentions are in the same chain.
  fsamechain(F,FM1,FM2) :-chainmention(F,C,FM1),chainmention(F,C,FM2), FM1 != FM2.
  cmsamechain(M1,M2) :- fsamechain(F,FM1,FM2), cfmention(F,FM1,M1), cfmention(F,FM2,M2), M1 < M2.

  % Amount of direct evidence from annotators for canonical mentions M1 and M2 to be in the same chain.
  evidence(M1,M2,Evidence) :- cmsamechain(M1,M2), Evidence > 0,
    Evidence = #count { F : fsamechain(F,FM1,FM2), cfmention(F,FM1,M1), cfmention(F,FM2,M2), FM1 < FM2 }.

  % Usage cost 1 for each annotators who did not put M1/M2 into same chain.
  cmusecost(M1,M2,N-K) :- cmsamechain(M1,M2), evidence(M1,M2,K), N-K > 0, numfiles(N).
  % Omission cost 2 for each annotator who put M1/M2 into the same chain.
  cmomitcost(M1,M2,2*K) :- cmsamechain(M1,M2), evidence(M1,M2,K).

  :~ not f. [1@1,foo]

  % require non-singleton chains
  :- resultchain(C), #count { Y : resultcm(C,Y) } <= 1.

  % forbid mentions within mentions in same chain
  :- resultcm(C,mid(From1,To1)), resultcm(C,mid(From2,To2)),
     From1 <= From2, To2 <= To1, (From1,To1) != (From2,To2).

  #show resultcm/2.
  '''

encoding_mm = '''
  % Links implicitly given by annotators.
  link(F,M1,M2) :-chainmention(F,C,M1),chainmention(F,C,M2), M1 < M2.

  % Guess which links to use.
  { uselink(File,M1,M2) } :- link(File,M1,M2).

  % Represent canonical mentions and links between them.
  %clink(MID1,MID2) :- uselink(File,M1,M2),
  %  mention(File,M1,From1,To1), mention(File,M2,From2,To2),
  %  MID1=mid(From1,To1), MID2=mid(From2,To2), MID1 < MID2.
  %clink(MID1,MID2) :- uselink(File,M2,M1),
  %  mention(File,M1,From1,To1), mention(File,M2,From2,To2),
  %  MID1=mid(From1,To1), MID2=mid(From2,To2), MID1 < MID2.
  clink(MID1,MID2) :- uselink(File,M1,M2),
    cfmention(File,M1,MID1), cfmention(File,M2,MID2), MID1 < MID2.
  clink(MID1,MID2) :- uselink(File,M2,M1),
    cfmention(File,M1,MID1), cfmention(File,M2,MID2), MID1 < MID2.

  % Reflexive symmetric transitive closure of clink/2.
  cc(X,Y) :- clink(X,Y).
  cc(X,Y) :- cc(Y,X).
  cc(X,Z) :- cc(X,Y), cc(Y,Z).

  % Smallest mention in one SCC of cc/2 becomes representative of the chain.
  notrepresentative(Y) :- cc(X,Y), X < Y.
  resultcm(X,Y) :- cc(X,Y), not notrepresentative(X).
  resultchain(C) :- resultcm(C,_).
  '''

encoding_cm = '''
  % We reuse lines 1-11 of MM encoding for guessing used links.
  link(F,M1,M2) :-chainmention(F,C,M1),chainmention(F,C,M2), M1 < M2.

  { uselink(File,M1,M2) } :- link(File,M1,M2).

  % canonical mentions and links between them
  clink(MID1,MID2) :- uselink(File,M1,M2),
    mention(File,M1,From1,To1), mention(File,M2,From2,To2),
    MID1=mid(From1,To1), MID2=mid(From2,To2), MID1 < MID2.
  clink(MID1,MID2) :- uselink(File,M2,M1),
    mention(File,M1,From1,To1), mention(File,M2,From2,To2),
    MID1=mid(From1,To1), MID2=mid(From2,To2), MID1 < MID2.

  % Obtain canonical mentions from clink/2.
  cmention(M) :- clink(M,_).  cmention(M) :- clink(_,M).

  % Highest number of chains in all files.
  countchain(File,N) :-chainmention(File,_,_), N = #count { C :chainmention(File,C,_) }.
  maxchain(N) :- N = #max { C : countchain(_,C) }.
  % Assume we will not need more than this amount of chains.
  chainlimit(N*6/5) :- maxchain(N).

  % Guess which chain IDs to use in result.
  { resultchain(X) : X = 1..Max } :- chainlimit(Max).
  resultchain(Y) :- resultchain(X), Y = 1..(X-1). % Symmetry breaking.

  % Guess which canonical mention becomes part of which chain.
  1 { resultcm(C,M) : resultchain(C) } 1 :- cmention(M).

  % Synchronize guessed result with clink/2.
  :- clink(X,Y), resultcm(C,X), not resultcm(C,Y).
  :- clink(X,Y), not resultcm(C,X), resultcm(C,Y).
  '''

encoding_forcing = '''
  % eliminate warnings if emptyline/1 is not defined
  emptyline(-1).
  % forced tokens
  forcetok(Line) :- emptyline(Line).
  forcetok(From) :- mention(forced,_,From,To).
  forcetok(To) :- mention(forced,_,From,To).

  % forbid extra (i.e., not forced) result mentions at forced lines
  :- forcetok(From), resultcm(_,mid(From,To)), not mention(forced,_,From,To).
  :- forcetok(To), resultcm(_,mid(From,To)), not mention(forced,_,From,To).

  % require that all forced mentions exist in the solution
  :- mention(forced,_,From,To), not resultcm(_,mid(From,To)).

  % ensure that pairs of mentions in same forced chain end up in the same result chain
  forcesame(MID1,MID2) :-
    chainmention(forced,C,M1), chainmention(forced,C,M2), M1 != M2,
    cfmention(forced,M1,MID1), cfmention(forced,M2,MID2), MID1 < MID2.
  :- forcesame(MID1,MID2), resultcm(C1,MID1), resultcm(C2,MID2), C1 != C2.

  % forbid that pairs of mentions in distinct forced chains are in the same chain
  forcedistinct(MID1,MID2) :-
    chainmention(forced,C1,M1), chainmention(forced,C2,M2), C1 < C2,
    cfmention(forced,M1,MID1), cfmention(forced,M2,MID2).
  :- forcedistinct(MID1,MID2), resultcm(C,MID1), resultcm(C,MID2).
  '''

# INTERESTING FUTURE TOPIC AND APPLICATION AREA FOR HEX!
#
#  % CHAIN IDS
#  % * this is very slow (grounding)
#  % * this is a classical case where splitting the program would help:
#  %   - find solution above without IDs
#  %   - run this lower part of encoding for assigning unique and continuous
#  %     integers to all chains in solution while not changing user-specified chain IDs
#  %     (note: user can provide solution but quality does not depend on IDs)
#  %     (note: IDs seem a detail, but in practice IDs are highly relevant!)
#  %
#  %% what is count of chains in each file
#  %file(File) :- chainmention(File,_,_).
#  %chaincount(File,N) :- file(File), N = #count { C : chainmention(File,C,_) }.
#  %% assume result number of chains is at most 2 * number of chains in file with most chains
#  %maxchainid(2*M) :- M = #max { N : chaincount(_,N) }.
#  %1 { chainid(Ch,1..N) } 1 :- resultchain(Ch), maxchainid(N).
#  %% require that each chain gets a different id
#  %:- chainid(Ch1,ChainId), chainid(Ch2,ChainId), Ch1 < Ch2. % require different Ids
#  %:~ chainid(Ch,ChainId). [ChainId@1,Ch] % optimize so that we get minimum Ids

encodings_core = {
  'mm':  encoding_common + encoding_mm,
  'cm':  encoding_common + encoding_cm,
}
encodings_obj = {
  'cm_u':   '''
            % [V, U, VA, UA] Cost for not using a link, corresponding to annotations.
            :~ not clink(M1,M2), cmomitcost(M1,M2,Cost). [Cost@1,M1,M2,omit]
            % [V, U        ] Forbid creating an implicit link that has not been annotated.
            :- resultcm(C,X), resultcm(C,Y), X < Y, not clink(X,Y).
            ''',
  'cm_ua':  '''
            % [V, U, VA, UA] Cost for not using a link, corresponding to annotations.
            :~ not clink(M1,M2), cmomitcost(M1,M2,Cost). [Cost@1,M1,M2,omit]
            % [      VA, UA] Minimize number of implicit links that have not been annotated.
            :~ resultcm(C,X), resultcm(C,Y), X < Y, not clink(X,Y). [1@1,X,Y]
            ''',
  'cm_v':   '''
            % [V, U, VA, UA] Cost for not using a link, corresponding to annotations.
            :~ not clink(M1,M2), cmomitcost(M1,M2,Cost). [Cost@1,M1,M2,omit]
            % [V,    VA    ] Cost for using a link, corresponding to non-annotations.
            :~ clink(M1,M2), cmusecost(M1,M2,Cost). [Cost@1,M1,M2,use]
            % [V, U        ] Forbid creating an implicit link that has not been annotated.
            :- resultcm(C,X), resultcm(C,Y), X < Y, not clink(X,Y).
            ''',
  'cm_va':  '''
            % [V, U, VA, UA] Cost for not using a link, corresponding to annotations.
            :~ not clink(M1,M2), cmomitcost(M1,M2,Cost). [Cost@1,M1,M2,omit]
            % [V,    VA    ] Cost for using a link, corresponding to non-annotations.
            :~ clink(M1,M2), cmusecost(M1,M2,Cost). [Cost@1,M1,M2,use]
            % [      VA, UA] Minimize number of implicit links that have not been annotated.
            :~ resultcm(C,X), resultcm(C,Y), X < Y, not clink(X,Y). [1@1,X,Y]
            ''',
  'mm_u':   '''
            % [V, U, VA, UA] Cost for not using a link, corresponding to annotations.
            :~ not clink(M1,M2), cmomitcost(M1,M2,Cost). [Cost@1,M1,M2,omit]
            % [V, U        ] Forbid creating an implicit link that has not been annotated.
            :- cc(X,Y), X < Y, not clink(X,Y).
            ''',
  'mm_ua':  '''
            % [V, U, VA, UA] Cost for not using a link, corresponding to annotations.
            :~ not clink(M1,M2), cmomitcost(M1,M2,Cost). [Cost@1,M1,M2,omit]
            % [      VA, UA] Minimize number of implicit links that have not been annotated.
            :~ cc(X,Y), X < Y, not clink(X,Y). [1@1,X,Y]
            ''',
  'mm_v':  '''
            % [V, U, VA, UA] Cost for not using a link, corresponding to annotations.
            :~ not clink(M1,M2), cmomitcost(M1,M2,Cost). [Cost@1,M1,M2,omit]
            % [V,    VA    ] Cost for using a link, corresponding to non-annotations.
            :~ clink(M1,M2), cmusecost(M1,M2,Cost). [Cost@1,M1,M2,use]
            % [V, U        ] Forbid creating an implicit link that has not been annotated.
            :- cc(X,Y), X < Y, not clink(X,Y).
            ''',
  'mm_va':  '''
            % [V, U, VA, UA] Cost for not using a link, corresponding to annotations.
            :~ not clink(M1,M2), cmomitcost(M1,M2,Cost). [Cost@1,M1,M2,omit]
            % [V,    VA    ] Cost for using a link, corresponding to non-annotations.
            :~ clink(M1,M2), cmusecost(M1,M2,Cost). [Cost@1,M1,M2,use]
            % [      VA, UA] Minimize number of implicit links that have not been annotated.
            :~ cc(X,Y), X < Y, not clink(X,Y). [1@1,X,Y]
            '''
}

rMId = re.compile(r'mid\(([0-9]+),([0-9]+)\)')
def extractMentionsChains(answerset):
  # key = chain id (from ASP, this is a compount term!)
  # value = set of mention id's
  chains = collections.defaultdict(set)
  mentions = {} # key = mention id, value = (fromline,toline)
  mid = 0
  for atm in answerset:
    if atm[0] == 'resultcm':
      cid, m = atm[1:]
      structuredmid = rMId.findall(m)
      #warn("mid {} structuredmid {}".format(m, repr(structuredmid)))
      mfrom, mto = map(int, structuredmid[0])
      mentions[mid] = (mfrom, mto)
      chains[cid].add(mid)
      #warn("found mid {}/{} in chain {}".format(mfrom, mto, cid))
      mid += 1
  return mentions, chains

def createResultLines(annotations, mentions, chains):
  '''
    result looks like this:
    {
      'lines': [ '1\t3\t...\t(2)', '3\t...\t-', ... ],
      'mentions': { id: (linefrom,lineto), ... },
      'chains': { id: set([id1,id2]), ... }
    }
  '''
  out = { 'lines': [], 'mentions': mentions, 'chains': chains }
  #warn('annotations '+repr(annotations))
  for lineproduct in zip(*[ ann[1]['lines'] for ann in annotations ]):
    #warn('lineproduct '+repr(lineproduct))
    # flatten
    thisline = [ x for y in lineproduct for x in y ]
    # add coreference column
    thisline.append(None)
    #warn('thisline '+repr(thisline))
    out['lines'].append(thisline)
  eraseIgnoredMentions(out['lines'], annotations)
  createCoreferences(out['lines'], chains, mentions)
  return out

def eraseIgnoredMentions(lines, annotations):
  '''
  if we ignore a mention in an annotation because it is a singleton mention we also remove it from the lines
  '''
  rInt = re.compile(r'[0-9]+')
  nanno = len(annotations)
  for annidx, ann in enumerate(annotations):
    #warn('annotation {} is {}'.format(annidx, repr(ann)))
    remainingchains = set(ann[1]['chains'].keys())
    #warn('annotation {} has remaining chains {}'.format(annidx, repr(remainingchains)))
    for line in lines:
      column = len(line)-1-nanno+annidx
      #warn('line is {}'.format(repr(line)))
      chainids = set([ int(x) for x in rInt.findall(line[column]) ])
      todelete = chainids - remainingchains
      for d in todelete:
        orig = line[column]
        new = re.sub(r'\({}\)'.format(d), '', orig)
        new = re.sub(r'\({}\b'.format(d), '', new)
        new = re.sub(r'\b{}\)'.format(d), '', new)
        if new == '':
          new = '-'
        line[column] = new
        if orig == new:
          warn('orig {} = new {} for deleting {} which should not happen'.format(orig, new, d))
        #warn('orig {} / new {} for deleting {}'.format(orig, new, d))

def createCoreferences(lines, chains, mentions):
  '''
  writes coreference into last column of lines
  '''
  # if multiple mentions start or end at the same place:
  # the longer ones start before and end after the shorter ones, for example:
  # (1(3(4
  # 4)
  # 3)
  # 1)
  # hence for ech record in out we first find all mentions beginning/ending here
  aux = [ {'starting':[], 'ending':[], 'unit':[]} for x in range(0,len(lines)) ]
  for cidx, chain in chains.items():
    #warn('cidx {} chain {}'.format(repr(cidx), repr(chain)))
    for mid in chain:
      mention = mentions[mid]
      startidx, endidx = mention
      augmention = {'chain': cidx, 'len': endidx-startidx+1}
      if augmention['len'] == 1:
        assert(startidx == endidx)
        aux[startidx]['unit'].append(augmention)
      else:
        aux[startidx]['starting'].append(augmention)
        aux[endidx]['ending'].append(augmention)
      #warn('for mention {} in chain {} startidx {} endidx {}:\n\tstarting = {}\n\tending={}\n\tunit={}'.format(
      #  mid, cidx, startidx, endidx, aux[startidx]['starting'], aux[endidx]['ending'], aux[startidx]['unit']))

  for o, l in zip(aux, lines):
    # starting sorted by length, descending
    starts = sorted(o['starting'], key = lambda x: -x['len'])
    # ending sorted by length, ascending
    ends = sorted(o['ending'], key = lambda x: x['len'])
    if len(ends) > 0 and len(starts) > 0:
      # we have ending and starting: first put ending, then unit, then starting
      corefstr = ''.join(
        [ '{})'.format(x['chain']) for x in ends ] +
        [ '({})'.format(x['chain']) for x in o['unit'] ] +
        [ '({}'.format(x['chain']) for x in starts])
    elif len(ends) == 0:
      # we have no ending: first put starting and then unit
      corefstr = ''.join(
        [ '({}'.format(x['chain']) for x in starts ] +
        [ '({})'.format(x['chain']) for x in o['unit'] ])
    elif len(starts) == 0:
      # we have no starts: first put unit then end
      corefstr = ''.join(
        [ '({})'.format(x['chain']) for x in o['unit'] ] +
        [ '{})'.format(x['chain']) for x in ends ])
    assert(l[-1] is None) # assume someone created empty places for the coref column
    if corefstr == '':
      l[-1] = '-'
    else:
      l[-1] = corefstr
  # no return

def createIntegerChainIds(chains, mentions, forcedannotation=None):
  '''
  input format chains: dict:
    key = chain id (from ASP, this might be a compound term!)
    value = set of mention id's
  input format mentions: dict:
    key = mention id (integer)
    value = tuple: (line index from, line index to)
  output format: dict:
    key = chain index (integer, respecting integers assigned in forced annotations)
    value = set of mention id's
  '''
  # first get mention-to-chain-id mapping from forced annotations
  m2ch = {}
  if forcedannotation:
    unused, fann = forcedannotation
    #warn('createIntegerChainIds fann '+repr(fann))
    for chid, chset in fann['chains'].items():
      for mid in chset:
        mfrom, mto = fann['mentions'][mid]
        key = (mfrom,mto)
        #assert(key not in m2ch) # otherwise we have duplicate mentions (that has to be prevented in ASP)
        m2ch[key] = chid
  #warn('m2ch (which mentions are forced to which chain id)'+repr(m2ch))
  #warn('chains '+repr(chains))
  #warn('mentions '+repr(mentions))
  chid2idx = {}
  ichains = {}
  # go through chains and look if chain has known (=forced) chain id, if yes register it
  for chainid, chainset in chains.items():
    forced_chain_id = None
    firstmention = (None, None, None)
    for mid in chainset:
      m = mentions[mid]
      if m in m2ch:
        # found a mention in this chain which is forced
        if forced_chain_id is None:
          # note forced ID
          forced_chain_id = m2ch[m]
          firstmention = (mid, m[0], m[1])
          chid2idx[chainid] = forced_chain_id
          ichains[forced_chain_id] = chainset
        else:
          # check forced ID
          if forced_chain_id != m2ch[m]:
            warn("found chain in result with two mentions forced to different chain IDs!")
            warn("  mention {} from {} to {} forced to chain {}".format(firstmention[0], firstmention[1], firstmention[2], forced_chain_id))
            warn("  mention {} from {} to {} forced to chain {}".format(mid, m[0], m[1], m2ch[m]))
            warn("  -> ignoring this forced assignment!")
        #break # done with this chain (break inner loop)
  #warn('chid2idx (forced only) '+repr(chid2idx))
  #warn('ichains (forced only) '+repr(ichains))
  # go over chains and if we don't know them, assign next free integer
  def nextChainId(ichains):
    nextchainidx = 1
    while nextchainidx in ichains:
      nextchainidx += 1
    return nextchainidx
  for chainid, chainset in chains.items():
    if chainid not in chid2idx:
      new_chain_id = nextChainId(ichains)
      chid2idx[chainid] = new_chain_id
      ichains[new_chain_id] = chainset
  #warn('chid2idx '+repr(chid2idx))
  #warn('ichains '+repr(ichains))
  return ichains

def consolidate(objective, doc, annotations, forcedannotation=None, config={}):
  '''
  This is the main contribution, here all the consolidation happens,
  either without or with "forced" annotations (= annotations that must exist as given in the output)

  Returns a dictionary doc -> lines
  '''
  if forcedannotation == []:
    forcedannotation = None
  facts = createInputFacts(annotations, forcedannotation)
  rep = config['representation']
  obj_key = rep+'_'+objective
  if rep not in encodings_core:
    raise Exception('could not find rep {} in encodings_core {}'.format(rep, repr(encodings_core.keys())))
  if obj_key not in encodings_obj:
    raise Exception('could not find objective {} in encodings_obj {}'.format(obj_key, repr(encodings_obj.keys())))
  aspparts = [encodings_core[rep], encodings_obj[obj_key]]
  if forcedannotation:
    aspparts.append(encoding_forcing)
  aspfacts = '\n'.join(facts)
  aspcode = '\n'.join(aspparts)
  if 'aspout' in config and config['aspout']:
    with open(config['aspout'], 'w+') as f:
      f.write(aspcode)
  if 'factout' in config and config['factout']:
    with open(config['factout'], 'w+') as f:
      f.write(aspfacts)
  if 'nocomp' in config and config['nocomp']:
    warn('terminated without computation because of --nocomp argument')
    sys.exit(2)
  answersets = runASP(aspfacts+aspcode, config)
  #warn('got answer sets '+repr(answersets))
  if len(answersets) == 1:
    docformat = '{doc}'
  else:
    docformat = '{doc}.{idx}'
  out = {}
  for idx, s in enumerate(answersets):
    mentions, chains = extractMentionsChains(s)
    #warn('got mentions '+repr(mentions))
    #warn('got chains '+repr(chains))
    ichains = createIntegerChainIds(chains, mentions, forcedannotation)
    lines = createResultLines(annotations, mentions, ichains)
    out[docformat.format(doc=doc, idx=idx)] = lines
  return out

def writeOutputTabs(f, results):
  #warn('writeOutput '+repr(results))
  colwidth = collections.defaultdict(int)
  for docname, docdict in results.items():
    #warn('docname {} docdict {}'.format(docname, repr(docdict)))
    f.write('#begin document ({});\n'.format(docname))
    for l in docdict['lines']:
      f.write('\t'.join(l)+'\n')
      for cidx, s in enumerate(l):
        colwidth[cidx] = max(colwidth[cidx], len(s))
    f.write('#end document\n')

  # create intelligent less
  tabs = []
  at = 0
  for colidx in range(0, len(colwidth)):
    at += colwidth[colidx] + 1
    tabs.append(str(at))
  lessstr = 'less -x' + ','.join(tabs)
  #warn(lessstr)
  return lessstr

def writeOutputTable(f, results):
  #warn('writeOutput '+repr(results))
  for docname, docdict in results.items():
    #warn('docname {} docdict {}'.format(docname, repr(docdict)))
    f.write('#begin document ({});\n'.format(docname))
    t = Table()
    for lidx, l in enumerate(docdict['lines']):
      for fidx, field in enumerate(l):
        t.cell(lidx, fidx, field)
    f.write(str(t)+'\n')
    f.write('#end document\n')
  return None

writeOutput = None
def configureOutputMethod(method):
  global writeOutput
  if method == 'tabs':
    writeOutput = writeOutputTabs
  elif method == 'table':
    writeOutput = writeOutputTable

configureOutputMethod(OUTPUTMETHOD)

def createBackup(filename):
  for i in itertools.count(start=1):
    backupname = '{}.{}.backup'.format(filename, i)
    if not os.path.exists(backupname):
      warn('writing backup of {} to {}'.format(filename, backupname))
      shutil.copyfile(filename, backupname)
      return

def writeResult(results, inout):
  warn("writing to file '{}'".format(inout))
  with open(inout, 'w+') as f:
    lessstr = writeOutput(f, results)

  if lessstr is not None:
    lesscmd = lessstr + ' ' + inout
    runLess = False
    if runLess:
      subprocess.call(lesscmd, shell=True)
    else:
      print('To view the result in Linux, you can use the following command:')
      print(lesscmd)

def writeResultIncludingForced(results, forcedannotation, inout):
  #warn('results '+repr(results))
  #warn('forcedannotation '+repr(forcedannotation))
  # results and forced annotations are parallel
  # modify results in place
  for res, forc in zip(results.items(), forcedannotation[1].items()):
    resname, resdict = res
    forcname, forcdict = forc
    atline = 1
    for rline, fline in zip(resdict['lines'], forcdict['lines']):
      # copy forced annotations from last column of fline to last column of rline
      # (assert that the forcing worked)
      fcoref = fline[-1]
      if fcoref[0].startswith('='):
        rcoref = rline[-1]
        if fcoref[1:] != rcoref:
          warn("forced annotation '{}' in line {} does not correspond to obtained '{}'".format(fcoref, atline, rcoref))
        rline[-1] = fcoref
      atline += 1
  # write out again
  writeResult(results, inout)

def detectClingo():
  global CLINGO
  try:
    p = subprocess.Popen(CLINGO, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
    out, err = p.communicate('')
    #warn('OUT\n'+out+'ERR\n'+err)
    if p.returncode != 30:
      p = subprocess.Popen('~/.local/bin/clingo', stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
      out, err = p.communicate('')
      if p.returncode != 30:
        raise Exception('returncode {} no clingo is found'.format(p.returncode))
      CLINGO = os.environ['HOME'] + '/.local/bin/clingo'
  except Exception as e:
    print('downloading clingo\'s binaries')
    p = subprocess.Popen('wget -P /tmp https://github.com/potassco/clingo/releases/download/v5.2.0/clingo-5.2.0-linux-x86_64.tar.gz', stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
    out, err = p.communicate('')
    if p.returncode != 0:
      raise Exception('Could not download clingo returncode {}'.format(p.returncode))

    print('instaling clingo\'s binaries')
    p = subprocess.Popen('tar xvzf /tmp/clingo-5.2.0-linux-x86_64.tar.gz --strip-components=1 -C ~/.local/bin clingo-5.2.0-linux-x86_64/gringo clingo-5.2.0-linux-x86_64/clingo clingo-5.2.0-linux-x86_64/clasp clingo-5.2.0-linux-x86_64/lpconvert clingo-5.2.0-linux-x86_64/reify', stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True)
    out, err = p.communicate('')
    if p.returncode != 0:
     raise Exception('Could not install clingo returncode {}'.format(p.returncode))
    CLINGO = os.environ['HOME'] + '/.local/bin/clingo'

def main():
  annotations, inout, mode, obj, config = interpretArguments(sys.argv[1:])

  annotationdata = [ readInput(x) for x in annotations ]
  #warn('annotationdata='+repr(annotationdata))
  if mode == 'redo':
    createBackup(inout)
    forcedannotation = readInput({'path':inout, 'columns':'last', 'corefcolumn':'last'}, onlyUser=True)
    results = consolidateAll(obj, annotationdata, forcedannotation, config)
    writeResult(results, inout+'.clean')
    writeResultIncludingForced(results, forcedannotation, inout)
  if mode == 'auto':
    results = consolidateAll(obj, annotationdata, [], config)
    writeResult(results, inout)

# should be in library, but easier to ship if in same file
class Table:
  def __init__(self,colsep=' '):
    self.data = {}
    self.cols = set()
    self.rows = set()
    self.colsep = colsep
    self.colwidths = collections.defaultdict(int)

  def cell(self, row, col, content, align='right'):
    assert(isinstance(row,int))
    assert(isinstance(col,int))
    assert(isinstance(content,str))
    key = (row,col)
    self.cols.add(col)
    self.rows.add(row)
    self.data[key] = (content, align)
    self.colwidths[col] = max(self.colwidths[col], len(content))
    #warn('cell {} {} set to {} {}'.format(row, col, content, align))

  def __str__(self):
    # we only use used cols/rows
    realcols = sorted(self.cols)
    realrows = sorted(self.rows)
    out = ''
    for ridx, r in enumerate(realrows):
      if ridx > 0:
        out += '\n'
      first = True
      for c in realcols:
        if not first:
          out += self.colsep
        first = False
        if (r,c) in self.data:
          data, align = self.data[(r,c)]
        else:
          data, align = '', 'left'
        if align == 'left':
          out += data.ljust(self.colwidths[c])
        if align == 'right':
          out += data.rjust(self.colwidths[c])
    #warn('output of length {}'.format(len(out)))
    return out

if __name__ == "__main__":
  main()
