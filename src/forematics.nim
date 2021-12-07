## Metamath Proof verifier written in Nim

import algorithm, deques, os, sequtils, sets, strformat, strutils, tables
proc error(msg: string) =
  echo msg
  quit()

type
  Symbol = uint32

  Tokens = ref object
    index: int
    text: string

  Frame = ref object
    consts: HashSet[Symbol]
    vars: HashSet[Symbol]
    d: HashSet[(Symbol, Symbol)]
    f: seq[(Symbol, Symbol)]
    fLabels: Table[Symbol, Symbol]
    e: seq[seq[Symbol]]
    eLabels: Table[seq[Symbol], Symbol]

  LabelKind = enum
    Simple
    Complex
  Label = ref object
    case kind: LabelKind
    of Simple:
      arr: seq[Symbol]
    of Complex:
      dm: HashSet[(Symbol, Symbol)]
      mandatoryHypStmts: Deque[(Symbol, Symbol)]
      hypStmts: seq[seq[Symbol]]
      stat: seq[Symbol]

  Verifier = ref object
    stack: seq[Frame]
    labels: Table[Symbol, (Symbol, Label)]
    onlyLabel: Symbol
    beginLabel: Symbol
    began: bool
    stopLabel: Symbol

var
  symbolMapping: Table[string, Symbol]
  symbolMappingRev: Table[Symbol, string]

# common symbols
const
  None = 0.Symbol
  A_SYM = 1.Symbol # $a
  F_SYM = 2.Symbol # $f
  P_SYM = 3.Symbol # $p
  D_SYM = 4.Symbol # $d
  E_SYM = 5.Symbol # $e
  V_SYM = 6.Symbol # $e
  C_SYM = 7.Symbol # $e

  EQ_SYM = 8.Symbol
  DOT_SYM = 9.Symbol
  OPEN_CRB_SYM = 10.Symbol
  CLOSE_CRB_SYM = 11.Symbol
  OPEN_PR_SYM = 12.Symbol
  CLOSE_PR_SYM = 13.Symbol
  OPEN_DPR_SYM = 14.Symbol
  CLOSE_DPR_SYM = 15.Symbol

proc `$`(s: Symbol): string =
  symbolMappingRev[s]

proc `$`(ss: seq[Symbol]): string =
  for s in ss:
    result.add symbolMappingRev[s]
    result.add ' '
  result.removeSuffix(' ')

proc sym(s: string): Symbol =
  if s in symbolMapping:
    return symbolMapping[s]
  result = symbolMapping.len.Symbol
  symbolMapping[s] = result
  symbolMappingRev[result] = s

proc newVerifier(): Verifier =
  result = Verifier()
  doAssert sym("") == None # Create None symbol
  doAssert sym("$a") == A_SYM
  doAssert sym("$f") == F_SYM
  doAssert sym("$p") == P_SYM
  doAssert sym("$d") == D_SYM
  doAssert sym("$e") == E_SYM
  doAssert sym("$v") == V_SYM
  doAssert sym("$c") == C_SYM

  doAssert sym("$=") == EQ_SYM
  doAssert sym("$.") == DOT_SYM

  doAssert sym("${") == OPEN_CRB_SYM
  doAssert sym("$}") == CLOSE_CRB_SYM
  doAssert sym("(") == OPEN_PR_SYM
  doAssert sym(")") == CLOSE_PR_SYM

  doAssert sym("$(") == OPEN_DPR_SYM
  doAssert sym("$)") == CLOSE_DPR_SYM

proc newTokens(fileName: string): Tokens =
  result = Tokens()
  result.text = readFile(fileName)

proc eatWhitespace(tokens: Tokens) =
  while tokens.index < tokens.text.len and
    tokens.text[tokens.index] in {' ', '\n'}:
    inc tokens.index

proc read(tokens: Tokens): Symbol =
  if tokens.index >= tokens.text.len:
    return None
  tokens.eatWhitespace()
  let start = tokens.index
  var token = ""
  while tokens.index < tokens.text.len and
    tokens.text[tokens.index] notin {' ', '\n'}:
    inc tokens.index
  token = tokens.text[start ..< tokens.index]
  return sym(token)

proc readc(tokens: Tokens): Symbol =

  # Skip comment text
  tokens.eatWhitespace()
  while tokens.index + 1 < tokens.text.len and
    tokens.text[tokens.index] == '$' and
    tokens.text[tokens.index+1] == '(':
    tokens.index += 2
    while tokens.index + 1 < tokens.text.len and
      (tokens.text[tokens.index] != '$' or
      tokens.text[tokens.index+1] != ')'):
        inc tokens.index
    tokens.index += 2
    tokens.eatWhitespace()

  result = tokens.read()

proc readStat(tokens: Tokens): seq[Symbol] =
  var token = tokens.readc()
  while token != DOT_SYM:
    result.add(token)
    token = tokens.readc()

proc push(stack: var seq[Frame]) =
  stack.add(Frame())

proc addConst(stack: var seq[Frame], token: Symbol) =
  var frame = stack[^1]
  if token in frame.consts:
    error("Const already defined in scope")
  if token in frame.vars:
    error("Const already defined as var in scope")
  frame.consts.incl(token)

proc addVar(stack: var seq[Frame], token: Symbol) =
  var frame = stack[^1]
  if token in frame.vars: error("Var already defined in scope")
  if token in frame.consts:
    error("Var already defined as const in scope")
  frame.vars.incl(token)

proc lookupConst(stack: var seq[Frame], token: Symbol): bool =
  for i in countdown(stack.len - 1, 0):
    if token in stack[i].consts:
      return true

proc lookupVar(stack: var seq[Frame], token: Symbol): bool =
  for i in countdown(stack.len - 1, 0):
    if token in stack[i].vars:
      return true

proc lookup_f(stack: var seq[Frame], variable: Symbol): Symbol =
  for frame in reversed(stack):
    if variable in frame.fLabels:
      return frame.fLabels[variable]
  error(&"Key error: {variable}")

proc lookup_d(stack: var seq[Frame], x, y: Symbol): bool =
  for frame in reversed(stack):
    if (min(x, y), max(x, y)) in frame.d:
      return true

proc lookup_e(stack: var seq[Frame], stmt: seq[Symbol]): Symbol =
  for frame in reversed(stack):
    if stmt in frame.eLabels:
      return frame.eLabels[stmt]
  error(&"Key error: {stmt}")

proc add_f(stack: var seq[Frame], variable, kind, label: Symbol) =
  if not stack.lookupVar(variable):
    error(&"Var in $f not defined: {variable}")
  if not stack.lookupConst(kind):
    error(&"Const in $f not defined {kind}")
  var frame = stack[^1]
  if variable in frame.fLabels:
    error(&"Var in $f already defined in scope")
  frame.f.add((variable, kind))
  frame.fLabels[variable] = label

proc add_e(stack: var seq[Frame], stat: seq[Symbol], label: Symbol) =
  var frame = stack[^1]
  frame.e.add(stat)
  frame.eLabels[stat] = label

proc add_d(stack: var seq[Frame], stat: seq[Symbol]) =
  var frame = stack[^1]
  for x in stat:
    for y in stat:
      if x != y:
        frame.d.incl((min(x, y), max(x, y)))

proc makeAssertion(stack: var seq[Frame], stat: seq[Symbol]): (
  HashSet[(Symbol, Symbol)],
  Deque[(Symbol, Symbol)],
  seq[seq[Symbol]],
  seq[Symbol]
) =
  var eHyps: seq[seq[Symbol]]
  for frame in stack:
    for eh in frame.e:
      eHyps.add(eh)

  var mandatoryVars: HashSet[Symbol]
  for hyp in eHyps & @[stat]:
    for token in hyp:
      if stack.lookupVar(token):
        mandatoryVars.incl(token)

  var dvs: HashSet[(Symbol, Symbol)]
  for frame in stack:
    for x in mandatoryVars:
      for y in mandatoryVars:
        let pair = (x, y)
        if pair in frame.d:
          dvs.incl((x, y))

  var fHyps: Deque[(Symbol, Symbol)]
  for frame in reversed(stack):
    for (v, k) in reversed(frame.f):
      if v in mandatoryVars:
        fHyps.addFirst((k, v))
        mandatoryVars.excl(v)

  result[0] = dvs
  result[1] = fHyps
  result[2] = eHyps
  result[3] = stat

proc decompressProof(verifier: Verifier, stat, proof: seq[Symbol]): seq[Symbol] =
  var (_, mandatoryHypStmts, hypStmts, _) = verifier.stack.makeAssertion(stat)

  var mandatoryHyps: seq[Symbol]
  for (k, v) in mandatoryHypStmts:
    mandatoryHyps.add(verifier.stack.lookup_f(v))

  var hyps: seq[Symbol]
  for s in hypStmts:
    hyps.add(verifier.stack.lookup_e(s))

  var
    labels = mandatoryHyps & hyps
    hypEnd = len(labels)
    proofEnd = proof.find(CLOSE_PR_SYM)
  labels.add proof[1 ..< proofEnd]

  var proofInts: seq[int]
  var currInt = 0
  for i in proofEnd + 1 ..< proof.len:
    for ch in $proof[i]:
      if ch == 'Z':
        proofInts.add(-1)
      elif 'A' <= ch and ch <= 'T':
        currInt = (20 * currInt + ord(ch) - ord('A') + 1)
        proofInts.add(currInt - 1)
        currInt = 0
      elif 'U' <= ch and ch <= 'Y':
        currInt = (5 * currInt + ord(ch) - ord('U') + 1)

  var
    labelEnd = len(labels)
    decompressedInts: seq[int]
    subProofs: seq[seq[int]]
    prevProofs: seq[seq[int]]

  for code in proofInts:
    if code == -1:
      subProofs.add(prevProofs[^1])
    elif 0 <= code and code < hypEnd:
      prevProofs.add(@[code])
      decompressedInts.add(code)
    elif hypEnd <= code and code < labelEnd:
      decompressedInts.add(code)
      var step = verifier.labels[labels[code]]
      var stepType = step[0]
      var stepData = step[1]

      if stepType in [A_SYM, P_SYM]:
        var
          vars = stepData.mandatoryHypStmts
          hyps = stepData.hypStmts
          newPrevProof: seq[int]
        var nsHyps = len(hyps) + len(vars)
        if nsHyps != 0:
          for p in prevProofs[prevProofs.len - nsHyps .. ^1]:
            for s in p:
              newPrevProof.add(s)
          newPrevProof.add @[code]
          prevProofs = prevProofs[0 ..< prevProofs.len - nsHyps]
        else:
          newPrevProof = @[code]
        prevProofs.add(newPrevProof)
      else:
        prevProofs.add(@[code])

    elif labelEnd <= code:
      var pf = subProofs[code - labelEnd]
      decompressedInts.add(pf)
      prevProofs.add(pf)

  for i in decompressedInts:
    result.add(labels[i])

proc applySubst(
  verifier: Verifier,
  stat: seq[Symbol],
  subst: Table[Symbol, seq[Symbol]]
): Label =
  var arr: seq[Symbol]
  for token in stat:
    if token in subst: arr.add(subst[token])
    else: arr.add(token)
  return Label(kind: Simple, arr: arr)

proc findVars(verifier: Verifier, stat: seq[Symbol]): seq[Symbol] =
  for x in stat:
    if x notin result and verifier.stack.lookupVar(x):
      result.add(x)

proc verify(verifier: Verifier, statLabel: Symbol, stat, proofIn: seq[Symbol]) =
  echo "Verifying ", statLabel
  var
    stack: seq[Label]
    proof = proofIn

  if proof[0] == OPEN_PR_SYM:
    proof = verifier.decompressProof(stat, proof)

  for label in proof:

    var
      stepType = verifier.labels[label][0]
      stepData = verifier.labels[label][1]

    if stepType in [A_SYM, P_SYM]:
      var
        distinctR = stepData.dm
        mandatoryVar = stepData.mandatoryHypStmts
        hyp = stepData.hypStmts
        resultR = stepData.stat

      var npop = mandatoryVar.len + hyp.len
      var sp = stack.len - npop
      if sp < 0:
        error("Stack underflow")

      var subst: Table[Symbol, seq[Symbol]]
      for (k, v) in mandatoryVar:
        var entry = stack[sp]
        doAssert entry.kind == Simple
        if entry.arr[0] != k:
          error(&"Stack entry ({k}, {v}) doesn't match mandatory var hyp {entry.arr}")
        subst[v] = entry.arr[1..^1]
        sp += 1

      if distinctR.len > 0:
        for (x, y) in distinctR:

          let xVars = verifier.findVars(subst[x])
          let yVars = verifier.findVars(subst[y])

          for x in xVars:
            for y in yVars:
              if x == y or not verifier.stack.lookup_d(x, y):
                error(&"Disjoint violation {x} {y}")

      for h in hyp:
        var entry = stack[sp]
        var substH = verifier.applySubst(h, subst)
        if entry.kind != substH.kind and entry.arr != substH.arr:
          error("Stack entry doesn't match hypothesis")
        sp += 1

      if stack.len != 0 and npop != 0:
        stack.delete((stack.len - npop) ..< stack.len)

      stack.add(verifier.applySubst(resultR, subst))

    elif stepType in [E_SYM, F_SYM]:
      stack.add(stepData)

  if stack.len != 1:
    error("Stack has >1 entry at end")

  if stack[0].arr != stat:
    error("Assertion proved doesn't match")

proc read(verifier: Verifier, tokens: Tokens) =
  verifier.stack.push()
  var
    label = None
    token = tokens.readc()
  while token != None and token != CLOSE_CRB_SYM:
    if token == C_SYM:
      for token in tokens.readStat():
        verifier.stack.addConst(token)

    elif token == V_SYM:
      for token in tokens.readStat():
        verifier.stack.addVar(token)

    elif token == F_SYM:
      var stat = tokens.readStat()
      if label == None: error("$f must have label")
      if stat.len != 2: error("$f must have be length 2")

      verifier.stack.add_f(stat[1], stat[0], label)
      verifier.labels[label] =
        (F_SYM, Label(kind: Simple, arr: @[stat[0], stat[1]]))
      label = None

    elif token == A_SYM:
      if label == None: error("$a must have label")
      if label == verifier.stopLabel: quit(0)
      let ass = verifier.stack.makeAssertion(tokens.readStat())
      verifier.labels[label] = (A_SYM, Label(kind: Complex,
        dm: ass[0],
        mandatoryHypStmts: ass[1],
        hypStmts: ass[2],
        stat: ass[3]
      ))
      label = None

    elif token == E_SYM:
      if label == None: error("$e must have label")
      var stat = tokens.readStat()
      verifier.stack.add_e(stat, label)
      verifier.labels[label] = (E_SYM, Label(kind: Simple, arr: stat))
      label = None

    elif token == P_SYM:
      if label == None: error("$p must have label")
      if label == verifier.stopLabel: quit(0)
      var stat = tokens.readStat()
      var proof: seq[Symbol]

      var i = stat.find(EQ_SYM)
      if i == -1:
        error("$p must contain proof after $=")
      proof = stat[i + 1 .. ^1]
      stat = stat[0 ..< i]

      if verifier.onlyLabel != None:
        if label == verifier.onlyLabel:
          verifier.verify(label, stat, proof)
      elif verifier.beginLabel != None:
        if label == verifier.beginLabel:
          verifier.began = true
        if verifier.began:
          verifier.verify(label, stat, proof)
      elif verifier.stopLabel != None:
        if label == verifier.stopLabel:
          verifier.verify(label, stat, proof)
        quit()
      else:
        verifier.verify(label, stat, proof)

      let ass = verifier.stack.makeAssertion(stat)

      verifier.labels[label] = (P_SYM, Label(kind: Complex,
        dm: ass[0],
        mandatoryHypStmts: ass[1],
        hypStmts: ass[2],
        stat: ass[3]
      ))
      label = None

    elif token == D_SYM:
      verifier.stack.add_d(tokens.readStat())

    elif token == OPEN_CRB_SYM:
      verifier.read(tokens)

    elif ($token)[0] != '$':
      label = token

    else:
      error("token: " & $token)

    token = tokens.readc()

  discard verifier.stack.pop()

when isMainModule:
  if paramCount() < 1:
    quit("forematics set.mm [start-symbol] [stop-symbol]")
  let tokens = newTokens(paramStr(1))
  let verifier = newVerifier()
  if paramCount() == 2:
    verifier.onlyLabel = paramStr(2).sym
  elif paramCount() == 3:
    verifier.beginLabel = paramStr(2).sym
    verifier.stopLabel = paramStr(3).sym
  verifier.read(tokens)
