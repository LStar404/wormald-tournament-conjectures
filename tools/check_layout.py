"""Verify the notation relocation against the pinned, pre-layout manuscripts.

All original mathematical expressions are conserved. Reversing the recorded
notation moves and two editorial changes must recover each original source hash.
This is a document check, independent of the unchanged Lean kernel checks.
"""
from collections import Counter
from pathlib import Path
import hashlib,json,re

ROOT=Path(__file__).resolve().parents[1]
RECORD=ROOT/'verification/qa/layout_relocation.json'
MATH=r'\$\$.*?\$\$|\$[^$\n]+\$|\\\[.*?\\\]|\\\(.*?\\\)'

def without_layout_markers(text):
    text=re.sub(r'(?m)^::: \{\.[^\n]+\}\n\n','',text)
    return re.sub(r'\n\n:::(?=\n|$)','',text)

def restore_and_check(name):
    record=json.loads(RECORD.read_text(encoding='utf-8'))['documents'][name]
    edited=(ROOT/'docs'/name).read_text(encoding='utf-8')
    assert hashlib.sha256(edited.encode()).hexdigest()==record['final_normalized_sha256'],('Unreviewed document',name)
    restored=edited
    for change in reversed(record.get('editorial_changes',[])):
        assert restored.count(change['new'])==1,(name,'Editorial change')
        restored=restored.replace(change['new'],change['old'])
    for item in reversed(record.get('insertion_audit',[])):
        at=item['offset'];content=item['content']
        assert restored[at:at+len(content)]==content,(name,'Relocation',at)
        restored=restored[:at]+restored[at+len(content):]
    for item in reversed(record.get('relocated_body_notation',[])):
        at=item['offset'];restored=restored[:at]+item['content']+restored[at:]
    if record.get('removed_front_region'):
        item=record['removed_front_region'];at=item['offset']
        restored=restored[:at]+item['content']+restored[at:]
    restored=without_layout_markers(restored)
    assert hashlib.sha256(restored.encode()).hexdigest()==record['baseline_normalized_sha256'],('Original body not recovered',name)
    assert Counter(re.findall(MATH,edited,re.S))==Counter(re.findall(MATH,restored,re.S)),('Math expression changed',name)
    return restored

def main():
    record=json.loads(RECORD.read_text(encoding='utf-8'))
    counts={name:len(re.findall(MATH,restore_and_check(name),re.S)) for name in record['documents']}
    print(json.dumps({'result':'passed','baseline_commit':record['source_commit'],
                     'original_math_expressions_preserved':counts,
                     'scope':'Reversible document edits and formula conservation; not a new mathematical proof.'},ensure_ascii=False))

if __name__=='__main__':main()
