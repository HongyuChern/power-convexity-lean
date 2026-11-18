#!/usr/bin/env python3
"""Check exact axiom reports, including Lean declaration names containing apostrophes.
Derived from unchanged check_axiom_file.py; only the quoted-name regex is widened.
All source/report bijection and the three-axiom whitelist checks are unchanged.
"""
from pathlib import Path
import json,re,sys
source,log=map(Path,sys.argv[1:3])
requested=[]; scope=[]
for line in source.read_text().splitlines():
    m=re.match(r'namespace (\S+)',line)
    if m: scope.append(m.group(1))
    if re.match(r'end(?:\s|$)',line) and scope: scope.pop()
    m=re.match(r'#print axioms (\S+)',line)
    if m:
        name=m.group(1)
        requested.append((tuple('.'.join(scope).split('.')) if scope else (),name))
text=log.read_text()
assert not re.search(r'sorryAx|error:|declaration uses .sorry',text)
reports=re.findall(r"^'(.+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)$",text,re.M)
reported={n for n,a in reports}
expected=[]
for namespace,name in requested:
    if name.startswith('_root_.'):
        candidates=[name.removeprefix('_root_.')]
    else:
        # Lean resolves a qualified relative name by searching enclosing
        # namespaces too (e.g. Problem.X inside Comparator.Check).
        candidates=['.'.join(namespace[:k]+(name,)) for k in range(len(namespace),-1,-1)]
    matches=[candidate for candidate in candidates if candidate in reported]
    assert matches,{'requested':name,'namespace':namespace,'candidates':candidates}
    expected.append(matches[0])
assert len(expected)==len(set(expected))==len(reports)
assert set(expected)==reported
allowed={'propext','Classical.choice','Quot.sound'}
for name,body in reports:
    actual={x.strip() for x in body.split(',') if x.strip()}
    assert actual<=allowed,(name,actual-allowed)
print(json.dumps({'status':'pass','source':str(source),'log':str(log),
                  'declarations':len(reports),'whitelist':sorted(allowed)}))
