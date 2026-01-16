import std/[json, tables, streams, algorithm, os, hashes]

type MergedEntry = object
  s2, s3: int
  axioms: seq[string]

proc main() =
  var atlas: Table[string, MergedEntry]
  
  let args = commandLineParams()
  if args.len == 0:
    stderr.writeLine("Usage: merge <file1.jsonl> <file2.jsonl> ...")
    quit(1)
  
  for filename in args:
    if not fileExists(filename):
      stderr.writeLine("File not found: " & filename)
      continue
    
    stderr.writeLine("Reading " & filename & "...")
    var lineCount = 0
    
    for line in lines(filename):
      if line.len == 0: continue
      try:
        let obj = parseJson(line)
        let fp = obj["fp"].getStr()
        let s2 = obj["s2"].getInt()
        let s3 = obj["s3"].getInt()
        
        if not atlas.hasKey(fp):
          atlas[fp] = MergedEntry(s2: s2, s3: s3, axioms: @[])
        
        for ax in obj["axioms"]:
          let axStr = ax.getStr()
          if atlas[fp].axioms.len < 20 and axStr notin atlas[fp].axioms:
            atlas[fp].axioms.add(axStr)
        
        lineCount.inc
      except:
        stderr.writeLine("Failed to parse line: " & line[0..min(50, line.len-1)])
    
    stderr.writeLine("  Loaded " & $lineCount & " entries")
  
  stderr.writeLine("\nTotal equivalence classes: " & $atlas.len)
  stderr.writeLine("Sorting...")
  
  var entries: seq[(string, MergedEntry)] = @[]
  for k, v in atlas: entries.add((k, v))
  
  # 按 (s3, s2) 升序排序
  entries.sort(proc (a, b: (string, MergedEntry)): int =
    result = cmp(a[1].s3, b[1].s3)
    if result == 0: result = cmp(a[1].s2, b[1].s2)
  )
  
  stderr.writeLine("Writing axioms_multi.txt...")
  
  var f = open("axioms_multi.txt", fmWrite)
  f.writeLine("# Groupoid Axiom Equivalence Classes (S2/S3 Only)")
  f.writeLine("# Sorted by (S3, S2) ascending")
  f.writeLine("")
  
  for (fp, entry) in entries:
    f.writeLine("--------------------------------------------------")
    f.writeLine("ID: " & fp & " | S2: " & $entry.s2 & " | S3: " & $entry.s3)
    for ax in entry.axioms:
      f.writeLine("  " & ax)
  
  f.close()
  stderr.writeLine("Done. Output: axioms_multi.txt")

main()
