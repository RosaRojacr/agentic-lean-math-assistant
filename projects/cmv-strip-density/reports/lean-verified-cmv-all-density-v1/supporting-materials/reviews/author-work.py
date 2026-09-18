import json, re
from pathlib import Path
base = Path(__file__).resolve().parents[1]
inv = json.loads((base/'declaration-inventory.json').read_text())
for source in sorted({d['source'] for d in inv['declarations']}):
    lines = (base/'lean'/source).read_text().splitlines()
    out=[]
    for i,d in enumerate(inv['declarations']):
        if d['source'] != source: continue
        text='\n'.join(lines[d['start_line']-1:d['end_line']])
        text=re.sub(r'/\-.*?\-/','',text,flags=re.S).strip()
        if d['kind'] in ('theorem','lemma'):
            text=re.split(r':=\s*(?:by\b)?',text,maxsplit=1)[0].strip()
        elif d['kind'] == 'structure':
            text=re.split(r'\n(?:namespace|end)\b',text,maxsplit=1)[0].strip()
        else:
            text=re.split(r'\n(?:theorem|lemma|namespace|end)\b',text,maxsplit=1)[0].strip()
        out.append(f"[{i}] {d['declaration']} ({d['start_line']}-{d['end_line']})\n{text}\n")
    (base/'reviews'/('author-excerpt-'+source+'.txt')).write_text('\n'.join(out))
print(f"Extracted {len(inv['declarations'])} inventoried source declarations.")
