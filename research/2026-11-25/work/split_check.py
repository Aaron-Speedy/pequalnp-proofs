"""Check third-party circuit certificates in resumable modules, preserving each declaration."""
import os,re,subprocess,sys
from pathlib import Path
src=Path(sys.argv[1]).resolve()
tag=sys.argv[2]
directory=src.parent/('checkparts'+tag)
directory.mkdir(exist_ok=True)
lines=src.read_text().splitlines(keepends=True)
outer=next(x.split()[1] for x in lines if x.startswith('namespace PEqualNP.Outside.'))
sections=[(0,[])]
stack=[]
for i,line in enumerate(lines):
    if re.match(r'namespace S_\d+',line):
        sections.append((i,stack.copy()))
    if line.startswith('theorem z') and re.match(r'theorem z\d+_(0|32|64|96|128|160) :',line):
        start=i
        while lines[start-1].startswith('set_option '):start-=1
        sections.append((start,stack.copy()))
    if line.startswith('namespace '):stack.append(line.strip().split()[1])
    elif line.startswith('end ') and stack:stack.pop()
sections.append((len(lines),[]))
env=os.environ.copy()
env['LEAN_PATH']=str(directory)+':'+env.get('LEAN_PATH','')
for j,((start,names),(end,closing)) in enumerate(zip(sections,sections[1:])):
    name=f'Circuit{tag}Part{j}'
    source=directory/(name+'.lean')
    obj=source.with_suffix('.olean')
    header='' if j==0 else f'import Circuit{tag}Part{j-1}\nopen PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds\n'+''.join('namespace '+n+'\n' for n in names)
    body=header+''.join(lines[start:end])+''.join('\nend '+n+'\n' for n in reversed(closing))
    if source.exists() and source.read_text()==body and obj.exists():continue
    source.write_text(body)
    print(name,start+1,end,flush=True)
    with source.with_suffix('.log').open('w') as log:
        subprocess.run(['lean','-R',str(directory),'-o',str(obj),str(source)],stdout=log,stderr=subprocess.STDOUT,env=env,check=True)
