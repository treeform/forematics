## Metamath Proof verifier written in Nim

import strutils, sequtils, sets, tables, algorithm, strformat, deques, os

proc error(msg: string) =
  echo msg
  quit()

type
  Symbol = int

  Tokens = ref object
    at: int
    text: string

  Frame = ref object
    c: HashSet[Symbol]
    v: HashSet[Symbol]
    d: HashSet[(Symbol, Symbol)]
    f: seq[(Symbol, Symbol)]
    f_labels: Table[Symbol, Symbol]
    e: seq[seq[Symbol]]
    e_labels: Table[seq[Symbol], Symbol]

  LabelKind = enum
    Simple
    Complex
  Label = ref object
    case kind: LabelKind
    of Simple:
      arr: seq[Symbol]
    of Complex:
      dm: HashSet[(Symbol, Symbol)]
      mand_hyp_stmts: Deque[(Symbol, Symbol)]
      hyp_stmts: seq[seq[Symbol]]
      stat: seq[Symbol]

  MM = ref object
    fs: seq[Frame]
    labels: Table[Symbol, (Symbol, Label)]
    only_label: Symbol
    begin_label: Symbol
    began: bool
    stop_label: Symbol

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

proc sym(s: string): Symbol =
  if s in symbolMapping:
    return symbolMapping[s]
  result = symbolMapping.len.Symbol
  symbolMapping[s] = result
  symbolMappingRev[result] = s

proc join(symbols: seq[Symbol]): string =
  for symbol in symbols:
    result.add $symbol

proc newMM(): MM =
  result = MM()
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

proc read(toks: Tokens): Symbol =
  if toks.at >= toks.text.len:
    return None
  while toks.text[toks.at] in {' ', '\n'}:
    inc toks.at
  let start = toks.at
  var token = ""
  while toks.text[toks.at] notin {' ', '\n'}:
    inc toks.at
  token = toks.text[start ..< toks.at]
  return sym(token)

proc readc(toks: Tokens): Symbol =
  result = toks.read()
  while result == OPEN_DPR_SYM:
    while result != CLOSE_DPR_SYM:
      result = toks.read()
    result = toks.read()

proc readstat(self: Tokens): seq[Symbol] =
  var tok = self.readc()
  while tok != DOT_SYM:
    result.add(tok)
    tok = self.readc()

proc push(fs: var seq[Frame]) =
  fs.add(Frame())

proc add_c(fs: var seq[Frame], tok: Symbol) =
  var frame = fs[^1]
  if tok in frame.c: error("const already defined in scope")
  if tok in frame.v:
    error("const already defined as var in scope")
  frame.c.incl(tok)

proc add_v(fs: var seq[Frame], tok: Symbol) =
  var frame = fs[^1]
  if tok in frame.v: error("const already defined in scope")
  if tok in frame.c:
    error("var already defined as const in scope")
  frame.v.incl(tok)

proc lookup_c(self: var seq[Frame], tok: Symbol): bool =
  for i in countdown(self.len - 1, 0):
    if tok in self[i].c:
      return true

proc lookup_v(self: var seq[Frame], tok: Symbol): bool =
  for i in countdown(self.len - 1, 0):
    if tok in self[i].v:
      return true

proc lookup_f(self: var seq[Frame], variable: Symbol): Symbol =
  for frame in reversed(self):
    if variable in frame.f_labels:
      return frame.f_labels[variable]
  error(&"Key error: {variable}")

proc lookup_d(self: var seq[Frame], x, y: Symbol): bool =
  for fr in reversed(self):
    if (min(x,y), max(x,y)) in fr.d:
      return true

proc lookup_e(self: var seq[Frame], stmt: seq[Symbol]): Symbol =
  for frame in reversed(self):
    if stmt in frame.e_labels:
      return frame.e_labels[stmt]
  error(&"Key error: {stmt}")

proc add_f(self: var seq[Frame], variable, kind, label: Symbol) =
  if not self.lookup_v(variable):
      error(&"var in $f not defined: {variable}")
  if not self.lookup_c(kind):
      error(&"const in $f not defined {kind}")
  var frame = self[^1]
  if variable in frame.f_labels:
      error(&"var in $f already defined in scope")
  frame.f.add((variable, kind))
  frame.f_labels[variable] = label

proc add_e(self: var seq[Frame], stat: seq[Symbol], label: Symbol) =
  var frame = self[^1]
  frame.e.add(stat)
  frame.e_labels[stat] = label

proc add_d(self: var seq[Frame], stat: seq[Symbol]) =
  var frame = self[^1]
  for x in stat:
    for y in stat:
      if x != y:
        frame.d.incl((min(x, y), max(x, y)))

proc make_assertion(self: var seq[Frame], stat: seq[Symbol]): (
  HashSet[(Symbol, Symbol)],
  Deque[(Symbol, Symbol)],
  seq[seq[Symbol]],
  seq[Symbol]
) =
  var e_hyps: seq[seq[Symbol]]
  for fr in self:
    for eh in fr.e:
      e_hyps.add(eh)

  var mand_vars: HashSet[Symbol]
  for hyp in e_hyps & @[stat]:
    for tok in hyp:
      if self.lookup_v(tok):
        mand_vars.incl(tok)

  var dvs: HashSet[(Symbol, Symbol)]
  for fr in self:
    for x in mand_vars:
      for y in mand_vars:
        let pair = (x, y)
        if pair in fr.d:
          dvs.incl((x, y))

  var f_hyps: Deque[(Symbol, Symbol)]
  for fr in reversed(self):
    for (v, k) in reversed(fr.f):
      if v in mand_vars:
        f_hyps.addFirst((k, v))
        mand_vars.excl(v)

  result[0] = dvs
  result[1] = f_hyps
  result[2] = e_hyps
  result[3] = stat

proc decompress_proof(self: MM, stat, proof: seq[Symbol]): seq[Symbol] =
  var (dm, mand_hyp_stmts, hyp_stmts, stat) = self.fs.make_assertion(stat)

  var mand_hyps: seq[Symbol]
  for (k, v) in mand_hyp_stmts:
    mand_hyps.add(self.fs.lookup_f(v))

  var hyps: seq[Symbol]
  for s in hyp_stmts:
    hyps.add(self.fs.lookup_e(s))

  var
    labels = mand_hyps & hyps
    hyp_end = len(labels)
    ep = proof.find(CLOSE_PR_SYM)
  labels.add proof[1 ..< ep]
  let compressed_proof = proof[ep+1 .. ^1].join()

  var proof_ints: seq[int]
  var cur_int = 0

  for ch in compressed_proof:
    if ch == 'Z':
      proof_ints.add(-1)
    elif 'A' <= ch and ch <= 'T':
      cur_int = (20 * cur_int + ord(ch) - ord('A') + 1)
      proof_ints.add(cur_int - 1)
      cur_int = 0
    elif 'U' <= ch and ch <= 'Y':
      cur_int = (5 * cur_int + ord(ch) - ord('U') + 1)

  var
    label_end = len(labels)
    decompressed_ints: seq[int]
    subproofs: seq[seq[int]]
    prev_proofs: seq[seq[int]]

  for pf_int in proof_ints:
      if pf_int == -1:
        subproofs.add(prev_proofs[^1])
      elif 0 <= pf_int and pf_int < hyp_end:
          prev_proofs.add(@[pf_int])
          decompressed_ints.add(pf_int)
      elif hyp_end <= pf_int and pf_int < label_end:
          decompressed_ints.add(pf_int)
          var step = self.labels[labels[pf_int]]
          var step_type = step[0]
          var step_data = step[1]

          if step_type in [A_SYM, P_SYM]:
              var
                svars = step_data.mand_hyp_stmts
                shyps = step_data.hyp_stmts
                new_prevpf: seq[int]
              var nshyps = len(shyps) + len(svars)
              if nshyps != 0:
                  for p in prev_proofs[prev_proofs.len - nshyps .. ^1]:
                    for s in p:
                      new_prevpf.add(s)
                  new_prevpf.add @[pf_int]

                  prev_proofs = prev_proofs[0 ..< prev_proofs.len - nshyps]
              else:
                new_prevpf = @[pf_int]
              prev_proofs.add(new_prevpf)
          else:
            prev_proofs.add(@[pf_int])

      elif label_end <= pf_int:
          var pf = subproofs[pf_int - label_end]
          decompressed_ints.add(pf)
          prev_proofs.add(pf)

  for i in decompressed_ints:
    result.add(labels[i])

proc apply_subst(self: MM, stat: seq[Symbol], subst: Table[Symbol, seq[Symbol]]): Label =
    var arr: seq[Symbol]
    for tok in stat:
        if tok in subst: arr.add(subst[tok])
        else: arr.add(tok)
    return Label(kind: Simple, arr:arr)

proc find_vars(self: MM, stat: seq[Symbol]): seq[Symbol] =
  for x in stat:
    if x notin result and self.fs.lookup_v(x):
      result.add(x)

proc verify(self: MM, stat_label: Symbol, stat, proofIn: seq[Symbol]) =
  echo "verifying ", stat_label
  var
    stack: seq[Label]
    proof = proofIn

  if proof[0] == OPEN_PR_SYM:
    proof = self.decompress_proof(stat, proof)

  for label in proof:

    var
      steptyp = self.labels[label][0]
      stepdat = self.labels[label][1]

    if steptyp in [A_SYM, P_SYM]:
      var
        distinctR = stepdat.dm
        mand_var = stepdat.mand_hyp_stmts
        hyp = stepdat.hyp_stmts
        resultR = stepdat.stat

      var npop = mand_var.len + hyp.len
      var sp = stack.len - npop
      if sp < 0:
        error("stack underflow")

      var subst: Table[Symbol, seq[Symbol]]
      for (k, v) in mand_var:
        var entry = stack[sp]
        doAssert entry.kind == Simple
        if entry.arr[0] != k:
          error(&"stack entry ({k}, {v}) doesn't match mandatory var hyp {entry.arr}")
        subst[v] = entry.arr[1..^1]
        sp += 1

      if distinctR.len > 0:
        for (x, y) in distinctR:

          let x_vars = self.find_vars(subst[x])
          let y_vars = self.find_vars(subst[y])

          for x in x_vars:
            for y in y_vars:
              if x == y or not self.fs.lookup_d(x, y):
                error(&"disjoint violation {x} {y}")

      for h in hyp:
        var entry = stack[sp]
        var subst_h = self.apply_subst(h, subst)
        if entry.kind != subst_h.kind and entry.arr != subst_h.arr:
          error("stack entry doesn't match hypothesis")
        sp += 1

      if stack.len != 0 and npop != 0:
        stack.delete((stack.len - npop) ..< stack.len)

      stack.add(self.apply_subst(resultR, subst))

    elif steptyp in [E_SYM, F_SYM]:
      stack.add(stepdat)

  if stack.len != 1:
    error("stack has >1 entry at end")

  if stack[0].arr != stat:
    error("assertion proved doesn't match")


proc read(self: MM, toks: Tokens) =
  self.fs.push()
  var
    label = None
    tok = toks.readc()
  while tok != None and tok != CLOSE_CRB_SYM:
    if tok == C_SYM:
      for tok in toks.readstat():
        self.fs.add_c(tok)

    elif tok == V_SYM:
      for tok in toks.readstat():
        self.fs.add_v(tok)

    elif tok == F_SYM:
      var stat = toks.readstat()
      if label == None: error("$f must have label")
      if stat.len != 2: error("$f must have be length 2")

      self.fs.add_f(stat[1], stat[0], label)
      self.labels[label] = (F_SYM, Label(kind: Simple, arr: @[stat[0], stat[1]]))
      # "labels f ", ff self.labels
      label = None

    elif tok == A_SYM:
      if label == None: error("$a must have label")
      if label == self.stop_label: quit(0)
      let ass = self.fs.make_assertion(toks.readstat())
      self.labels[label] = (A_SYM, Label(kind: Complex,
        dm: ass[0],
        mand_hyp_stmts: ass[1],
        hyp_stmts: ass[2],
        stat: ass[3]
      ))
      label = None

    elif tok == E_SYM:
      if label == None: error("$e must have label")
      var stat = toks.readstat()
      self.fs.add_e(stat, label)
      self.labels[label] = (E_SYM, Label(kind: Simple, arr:stat))
      label = None

    elif tok == P_SYM:
      if label == None: error("$p must have label")
      if label == self.stop_label: quit(0)
      var stat = toks.readstat()
      var proof: seq[Symbol]

      var i = stat.find(EQ_SYM)
      if i == -1:
        error("$p must contain proof after $=")
      proof = stat[i + 1 .. ^1]
      stat = stat[0 ..< i]

      if self.only_label != None:
        if label == self.only_label:
          self.verify(label, stat, proof)
      elif self.begin_label != None:
        if label == self.begin_label:
          self.began = true
        if self.began:
          self.verify(label, stat, proof)
      elif self.stop_label != None:
        if label == self.stop_label:
          self.verify(label, stat, proof)
        quit()
      else:
        self.verify(label, stat, proof)

      let ass = self.fs.make_assertion(stat)

      self.labels[label] = (P_SYM, Label(kind: Complex,
        dm: ass[0],
        mand_hyp_stmts: ass[1],
        hyp_stmts: ass[2],
        stat: ass[3]
      ))
      label = None

    elif tok == D_SYM:
      self.fs.add_d(toks.readstat())

    elif tok == OPEN_CRB_SYM:
      self.read(toks)

    elif ($tok)[0] != '$':
      label = tok

    else:
      error("tok: " & $tok)

    tok = toks.readc()

  discard self.fs.pop()

when isMainModule:
  if paramCount() < 1:
    quit("forematics set.mm [start-symbol] [stop-symbol]")
  let toks = newTokens(paramStr(1))
  let mm = newMM()
  if paramCount() == 2:
    mm.only_label = paramStr(2).sym
  elif paramCount() == 3:
    mm.begin_label = paramStr(2).sym
    mm.stop_label = paramStr(3).sym
  mm.read(toks)
