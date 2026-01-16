import std/[streams, strutils, sequtils, tables, hashes, math, bitops, os, algorithm, json]
import checksums/sha1

const 
  ScanDepth = 6

type
  Token = int8 
  Expr = seq[Token]
  ParVal3 = tuple[lo, hi: uint64]
  
  Chunk3 = object
    masksLo: array[3, array[3, uint64]]
    masksHi: array[3, array[3, uint64]]
  
  AxiomEntry = object
    sat2, sat3: int
    axioms: seq[string]

proc updateU64(ctx: var Sha1State; val: uint64) {.inline.} =
  var buf: array[8, char]
  var v = val
  for i in 0..7:
    buf[i] = char((v shr (i * 8)) and 0xFF)
  update(ctx, buf)

# ============== Size 2 ==============
var chunks2: seq[uint64]
var totalModels2: int32 = 0
var inputs2: seq[array[3, int]]

proc initInputs2() =
  for i in 0 ..< 8:
    var row: array[3, int]
    var tmp = i
    for v in 0..2:
      row[v] = tmp and 1
      tmp = tmp shr 1
    inputs2.add(row)

proc loadModels2(filename: string) =
  if not fileExists(filename): 
    stderr.writeLine("[Size2] File not found: " & filename)
    return
  var fs = newFileStream(filename, fmRead)
  let cnt = fs.readInt32()
  totalModels2 = cnt
  var buf = newSeq[int8](4)
  var chunk: uint64 = 0
  var inC = 0
  for i in 0..<cnt:
    discard fs.readData(addr buf[0], 4)
    var modelBits: uint64 = 0
    for j in 0..3:
      if buf[j] == 1: modelBits = modelBits or (1'u64 shl j)
    chunk = chunk or (modelBits shl (inC * 4))
    inC.inc
    if inC == 16:
      chunks2.add(chunk)
      chunk = 0
      inC = 0
  if inC > 0: chunks2.add(chunk)
  fs.close()
  stderr.writeLine("[Size2] Loaded " & $totalModels2 & " models")

proc updateFingerprint2(lhs, rhs: Expr; ctx: var Sha1State): int =
  var totalSat = 0
  
  for chunkIdx in 0 ..< chunks2.len:
    let chunkData = chunks2[chunkIdx]
    var mask: uint64 = 0
    let modelsInChunk = 
      if chunkIdx == chunks2.high: 
        (if totalModels2 mod 16 == 0: 16 else: int(totalModels2 mod 16))
      else: 16
    
    for m in 0 ..< modelsInChunk:
      let table = (chunkData shr (m * 4)) and 0xF
      var sat = true
      for inp in inputs2:
        var stackL: array[32, int]
        var spL = 0
        for ii in countdown(lhs.len-1, 0):
          if lhs[ii] >= 0: stackL[spL] = inp[lhs[ii]]; spL.inc
          else:
            spL.dec; let a = stackL[spL]
            spL.dec; let b = stackL[spL]
            stackL[spL] = int((table shr (a * 2 + b)) and 1); spL.inc
        var stackR: array[32, int]
        var spR = 0
        for ii in countdown(rhs.len-1, 0):
          if rhs[ii] >= 0: stackR[spR] = inp[rhs[ii]]; spR.inc
          else:
            spR.dec; let a = stackR[spR]
            spR.dec; let b = stackR[spR]
            stackR[spR] = int((table shr (a * 2 + b)) and 1); spR.inc
        if stackL[0] != stackR[0]: sat = false; break
      if sat: mask = mask or (1'u64 shl m); totalSat.inc
    
    updateU64(ctx, mask)
  
  totalSat

# ============== Size 3 ==============
var chunks3: seq[Chunk3]
var totalModels3: int32 = 0
var inputs3: seq[array[3, ParVal3]]

proc initInputs3() =
  for i in 0 ..< 27:
    var tmp = i
    var row: array[3, ParVal3]
    for v in 0..2:
      let val = tmp mod 3
      tmp = tmp div 3
      if val == 0: row[v] = (0'u64, 0'u64)
      elif val == 1: row[v] = (high(uint64), 0'u64)
      else: row[v] = (0'u64, high(uint64))
    inputs3.add(row)

func toBits3(val: int): ParVal3 =
  if val == 1: (1'u64, 0'u64)
  elif val == 2: (0'u64, 1'u64)
  else: (0'u64, 0'u64)

proc loadModels3(filename: string) =
  if not fileExists(filename):
    stderr.writeLine("[Size3] File not found: " & filename)
    return
  var fs = newFileStream(filename, fmRead)
  let cnt = fs.readInt32()
  totalModels3 = cnt
  var buf = newSeq[int8](9)
  var c = Chunk3()
  var inC = 0
  for i in 0..<cnt:
    discard fs.readData(addr buf[0], 9)
    let bit = 1'u64 shl inC
    for r in 0..2:
      for col in 0..2:
        let (lo, hi) = toBits3(buf[r*3+col].int)
        if lo > 0: c.masksLo[r][col] = c.masksLo[r][col] or bit
        if hi > 0: c.masksHi[r][col] = c.masksHi[r][col] or bit
    inC.inc
    if inC == 64:
      chunks3.add(c)
      c = Chunk3()
      inC = 0
  if inC > 0: chunks3.add(c)
  fs.close()
  stderr.writeLine("[Size3] Loaded " & $totalModels3 & " models")

func parallelOp3(l, r: ParVal3; c: ptr Chunk3): ParVal3 {.inline.} =
  let l0 = not l.lo and not l.hi
  let l1 = l.lo and not l.hi
  let l2 = not l.lo and l.hi
  let r0 = not r.lo and not r.hi
  let r1 = r.lo and not r.hi
  let r2 = not r.lo and r.hi
  var resLo, resHi: uint64 = 0
  resLo = resLo or (l0 and r0 and c.masksLo[0][0])
  resHi = resHi or (l0 and r0 and c.masksHi[0][0])
  resLo = resLo or (l0 and r1 and c.masksLo[0][1])
  resHi = resHi or (l0 and r1 and c.masksHi[0][1])
  resLo = resLo or (l0 and r2 and c.masksLo[0][2])
  resHi = resHi or (l0 and r2 and c.masksHi[0][2])
  resLo = resLo or (l1 and r0 and c.masksLo[1][0])
  resHi = resHi or (l1 and r0 and c.masksHi[1][0])
  resLo = resLo or (l1 and r1 and c.masksLo[1][1])
  resHi = resHi or (l1 and r1 and c.masksHi[1][1])
  resLo = resLo or (l1 and r2 and c.masksLo[1][2])
  resHi = resHi or (l1 and r2 and c.masksHi[1][2])
  resLo = resLo or (l2 and r0 and c.masksLo[2][0])
  resHi = resHi or (l2 and r0 and c.masksHi[2][0])
  resLo = resLo or (l2 and r1 and c.masksLo[2][1])
  resHi = resHi or (l2 and r1 and c.masksHi[2][1])
  resLo = resLo or (l2 and r2 and c.masksLo[2][2])
  resHi = resHi or (l2 and r2 and c.masksHi[2][2])
  (resLo, resHi)

func eval3(e: Expr; inputs: array[3, ParVal3]; c: ptr Chunk3): ParVal3 =
  var stack: array[32, ParVal3]
  var sp = 0
  for i in countdown(e.len-1, 0):
    let t = e[i]
    if t >= 0: stack[sp] = inputs[t]; sp.inc
    else:
      sp.dec; let vL = stack[sp]
      sp.dec; let vR = stack[sp]
      stack[sp] = parallelOp3(vL, vR, c); sp.inc
  stack[0]

proc updateFingerprint3(lhs, rhs: Expr; ctx: var Sha1State): int =
  var totalSat = 0
  
  for i in 0 ..< chunks3.len:
    let c = addr chunks3[i]
    var mask: uint64 = high(uint64)
    for inp in inputs3:
      let vL = eval3(lhs, inp, c)
      let vR = eval3(rhs, inp, c)
      mask = mask and not ((vL.lo xor vR.lo) or (vL.hi xor vR.hi))
      if mask == 0: break
    if i == chunks3.high:
      let validCount = totalModels3 mod 64
      if validCount > 0: mask = mask and ((1'u64 shl validCount) - 1)
    totalSat += countSetBits(mask)
    updateU64(ctx, mask)
  
  totalSat

# ============== Common ==============
func toStr(e: Expr): string =
  var s: seq[string] = @[]
  for x in countdown(e.len-1, 0):
    if e[x] >= 0: s.add("v" & $e[x])
    else:
      let a = s.pop(); let b = s.pop()
      s.add("(" & a & "*" & b & ")")
  s[0]

func isValidVarSet(e: Expr): bool =
  var seen, maxV: int = 0
  maxV = -1
  for t in e:
    if t >= 0:
      seen = seen or (1 shl t)
      if t > maxV: maxV = int(t)
  if maxV == -1: return false
  seen == (1 shl (maxV + 1)) - 1

proc main() =
  let args = commandLineParams()
  let totalShards = if args.len > 0: parseInt(args[0]) else: 1
  let shardId = if args.len > 1: parseInt(args[1]) else: 0
  
  stderr.writeLine("[Shard " & $shardId & "/" & $totalShards & "] Starting...")
  
  initInputs2()
  initInputs3()
  loadModels2("models2.bin")
  loadModels3("models3.bin")
  
  stderr.writeLine("\n>>> Generating Terms (Depth " & $ScanDepth & ")...")
  var termPool: seq[Expr] = @[]
  var layers = newSeq[seq[Expr]](ScanDepth + 1)
  layers[0] = @[]
  for v in 0..2: layers[0].add(@[Token(v)])
  termPool.add(layers[0])
  for d in 1 .. ScanDepth:
    layers[d] = @[]
    for k in 0 ..< d:
      for l in layers[k]:
        for r in layers[d - 1 - k]:
          var ex = @[Token(-1)]
          ex.add(l)
          ex.add(r)
          layers[d].add(ex)
          termPool.add(ex)
  stderr.writeLine("    Terms: " & $termPool.len)
  
  stderr.writeLine("\n>>> Mapping...")
  var localAtlas: Table[string, AxiomEntry]
  var pairIdx = 0
  var processed = 0
  
  let sep: array[1, char] = ['\xFE']
  
  for i in 0 ..< termPool.len:
    if not isValidVarSet(termPool[i]): continue
    for j in i + 1 ..< termPool.len:
      if not isValidVarSet(termPool[j]): continue
      
      if pairIdx mod totalShards == shardId:
        let lhs = termPool[i]
        let rhs = termPool[j]
        
        var ctx = newSha1State()
        
        let sat2 = if totalModels2 > 0: updateFingerprint2(lhs, rhs, ctx) else: 0
        update(ctx, sep)
        let sat3 = if totalModels3 > 0: updateFingerprint3(lhs, rhs, ctx) else: 0
        
        let fpHash = $finalize(ctx)
        
        # 过滤条件：sat3 不为 0 且不为全部（即有区分度）
        let interesting = totalModels3 > 0 and sat3 > 0 and sat3 < int(totalModels3)
        
        if interesting:
          let s1 = toStr(lhs)
          let s2 = toStr(rhs)
          let axStr = if s1 < s2: s1 & " == " & s2 else: s2 & " == " & s1
          
          if not localAtlas.hasKey(fpHash):
            localAtlas[fpHash] = AxiomEntry(sat2: sat2, sat3: sat3, axioms: @[])
          if localAtlas[fpHash].axioms.len < 20 and axStr notin localAtlas[fpHash].axioms:
            localAtlas[fpHash].axioms.add(axStr)
        
        processed.inc
        if processed mod 10000 == 0:
          stderr.write("\r    Processed: " & $processed)
          stderr.flushFile()
      
      pairIdx.inc
  
  stderr.writeLine("\n\n>>> Outputting " & $localAtlas.len & " equivalence classes...")
  
  for fpHash, entry in localAtlas:
    echo $(%*{
      "fp": fpHash,
      "s2": entry.sat2,
      "s3": entry.sat3,
      "axioms": entry.axioms
    })
  
  stderr.writeLine("[Shard " & $shardId & "] Done.")

main()
