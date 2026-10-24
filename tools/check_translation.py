"""Check mathematical and structural alignment of the complete bilingual papers."""
from pathlib import Path
from collections import Counter
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[1]
zh=(ROOT/"docs/paper.zh.md").read_text(encoding="utf-8")
en=(ROOT/"docs/paper.en.md").read_text(encoding="utf-8")
published={"zh":zh,"en":en}
relocation_record=ROOT/"verification/qa/layout_relocation.json"
if relocation_record.exists():
    from check_layout import restore_and_check
    # The two languages may introduce notation in different prose sentences.
    # Restore those reversible moves before the original sequence/block checks.
    # restore_and_check also binds the final text and every formula to its source.
    zh=restore_and_check("paper.zh.md")
    en=restore_and_check("paper.en.md")
pattern=r"\$\$.*?\$\$|\$[^$\n]+\$"
zm=re.findall(pattern,zh,re.S)
em=re.findall(pattern,en,re.S)
labels={"全部二维块":"all two-dimensional blocks",
        r"\rm 奇":r"\rm odd",
        "等号当且仅当 ":"with equality if and only if ",
        r"\mathcal R\text{ 的每个样本}":r"\text{each sample of }\mathcal R",
        r"\text{圈}":r"\text{cycles}",r"\text{路径}":r"\text{paths}"}
converted=[]
for value in zm:
    for a,b in labels.items():
        value=value.replace(a,b)
    converted.append(value)
assert converted==em,"Mathematical spans differ or occur in a different order"
final_zh=re.findall(pattern,published["zh"],re.S)
for a,b in labels.items():final_zh=[value.replace(a,b) for value in final_zh]
assert Counter(final_zh)==Counter(re.findall(pattern,published["en"],re.S)),"Published mathematical spans differ"
def block_types(text):
    masked=re.sub(pattern,"@@M@@",text,flags=re.S)
    blocks=re.split(r"\n\s*\n",masked.strip())
    return ["math" if block=="@@M@@" else "prose" for block in blocks]
assert block_types(zh)==block_types(en),"Prose/display block structure differs"
assert len(re.findall(r"(?m)^#{1,2} ",zh))==len(re.findall(r"(?m)^#{1,2} ",en))
assert not re.search(r"[\u4e00-\u9fff]|@@M|\[P\d{3}\]",published["en"])
assert not re.search(r"显然|同理",published["zh"])
assert not re.search(r"\b(obviously|clearly|similarly|analogously)\b",published["en"],re.I)
result={"result":"passed","mathematical_spans_each":len(zm),
        "prose_blocks_each":block_types(zh).count("prose"),
        "headings_each":len(re.findall(r"(?m)^#{1,2} ",zh)),
        "translated_mathematical_labels":labels,
        "sha256":{k:hashlib.sha256(v.encode()).hexdigest() for k,v in published.items()},
        "notation_relocation_verified":relocation_record.exists(),
        "published_headings_each":len(re.findall(r"(?m)^#{1,2} ",published["zh"])),
        "scope":"Published formulas conserved; original formula sequence and prose/display structure checked after hash-verified reversal of notation moves. Not independent mathematical or linguistic certification."}
(ROOT/"verification/qa/translation_alignment.json").write_text(json.dumps(result,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
print(json.dumps(result,ensure_ascii=True))
