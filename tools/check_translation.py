"""Check mathematical and structural alignment of the complete bilingual papers."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[1]
zh=(ROOT/"docs/paper.zh.md").read_text(encoding="utf-8")
en=(ROOT/"docs/paper.en.md").read_text(encoding="utf-8")
pattern=r"\$\$.*?\$\$|\$[^$\n]+\$"
zm=re.findall(pattern,zh,re.S)
em=re.findall(pattern,en,re.S)
labels={"全部二维块":"all two-dimensional blocks",
        r"\rm 奇":r"\rm odd",
        "等号当且仅当 ":"with equality if and only if "}
converted=[]
for value in zm:
    for a,b in labels.items():
        value=value.replace(a,b)
    converted.append(value)
assert converted==em,"Mathematical spans differ or occur in a different order"
assert len(re.findall(r"(?m)^#{1,2} ",zh))==len(re.findall(r"(?m)^#{1,2} ",en))
assert not re.search(r"[\u4e00-\u9fff]|@@M|\[P\d{3}\]",en)
assert not re.search(r"显然|同理",zh)
assert not re.search(r"\b(obviously|clearly|similarly|analogously)\b",en,re.I)
result={"result":"passed","mathematical_spans_each":len(zm),
        "headings_each":len(re.findall(r"(?m)^#{1,2} ",zh)),
        "translated_mathematical_labels":labels,
        "sha256":{k:hashlib.sha256(v.encode()).hexdigest() for k,v in {"zh":zh,"en":en}.items()},
        "scope":"Formula sequence and structural alignment; not independent mathematical or linguistic certification."}
(ROOT/"verification/qa/translation_alignment.json").write_text(json.dumps(result,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
print(json.dumps(result,ensure_ascii=True))
