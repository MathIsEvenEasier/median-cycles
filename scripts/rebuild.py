#!/usr/bin/env python3
"""Rebuild this project's source inside a pinned mathlib checkout on Azure."""
import hashlib,json,os,pathlib,re,shutil,subprocess,sys,time
root=pathlib.Path(__file__).resolve().parents[1]
work=pathlib.Path(sys.argv[1]).resolve()
if not pathlib.Path('/run/mathiseasy-azure-verified').is_file():
    raise SystemExit('Use the bounded Azure worker; this script refuses local compilation.')
proof=work/'median-rebuild-output';proof.mkdir(exist_ok=False)
modules='Projection Antipodal Cyclic Lattice Result FlipBound Audit'.split()
records=[]
for source in (root/'formal').glob('*.lean'):
    text=source.read_text()
    # Project files contain ordinary Lean declarations and kernel-checked proofs.
    if re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b',text):
        raise SystemExit('Forbidden project-source token: '+source.name)
    shutil.copy2(source,proof/source.name)
try:
    for module in modules+['NegativeControl']:
        negative=module=='NegativeControl';begin=time.monotonic()
        p=subprocess.run(['lake','env','lean','-j1','-M6000','-DwarningAsError=true','-DElab.async=false',
            '-o',str(proof/(module+'.olean')),str(proof/(module+'.lean'))],cwd=work,
            env=dict(os.environ,LEAN_PATH=str(proof)),capture_output=True,text=True,timeout=180)
        log=p.stdout+p.stderr
        records.append({'module':module,'exit_code':p.returncode,'log':log,'expected_failure':negative,
            'source_sha256':hashlib.sha256((proof/(module+'.lean')).read_bytes()).hexdigest(),
            'seconds':round(time.monotonic()-begin,3)})
        (proof/'rebuild-record.json').write_text(json.dumps(records,indent=2)+'\n')
        print(module+': exit '+str(p.returncode),flush=True)
        if p.returncode or module=='Audit':print(log,flush=True)
        if negative:
            if not (p.returncode==1 and 'type mismatch' in log.lower() and 'True.intro' in log and 'False' in log):
                raise RuntimeError('Negative control failed for an unexpected reason')
        elif p.returncode:raise RuntimeError('Positive module failed: '+module)
        if module=='Audit':
            entries=re.findall(r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)",log,re.S)
            if len(entries)!=10:raise RuntimeError('Incomplete declaration audit')
            for name,axioms in entries:
                if set(a.strip() for a in axioms.split(',') if a.strip())-{'propext','Classical.choice','Quot.sound'}:
                    raise RuntimeError('Unexpected axiom: '+name)
finally:
    (proof/'rebuild-record.json').write_text(json.dumps(records,indent=2)+'\n')
