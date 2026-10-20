"""Check published file hashes, local Markdown links and check-record status."""
from pathlib import Path
from urllib.parse import unquote
import hashlib,json,re

ROOT=Path(__file__).resolve().parents[1]
manifest=json.loads((ROOT/"MANIFEST.json").read_text(encoding="utf-8"))
alignment=json.loads((ROOT/"verification/qa/translation_alignment.json").read_text(encoding="utf-8"))
assert alignment["result"]=="passed"
for lang in ("zh","en"):
    normalized=(ROOT/f"docs/paper.{lang}.md").read_text(encoding="utf-8").encode("utf-8")
    assert hashlib.sha256(normalized).hexdigest()==alignment["sha256"][lang],("Stale translation review",lang)
current_reviews=[]
for name in ("style_review.json","definitions_calculation_review.json"):
    review_path=ROOT/"verification/qa"/name
    if review_path.exists():
        candidate=json.loads(review_path.read_text(encoding="utf-8"))
        if candidate["version"]==manifest["version"]:
            current_reviews.append(candidate)
assert current_reviews,"No review bound to the current manifest version"
for current in current_reviews:
    assert current["review_status"]=="completed"
    for name,expected in current["source_bytes_sha256"].items():
        assert hashlib.sha256((ROOT/"docs"/name).read_bytes()).hexdigest()==expected,("Stale source review",name)
for row in manifest["files"]:
    path=ROOT/row["path"]
    data=path.read_bytes()
    assert len(data)==row["bytes"],row["path"]
    assert hashlib.sha256(data).hexdigest()==row["sha256"],row["path"]
    assert hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()==row["git_blob_sha1"]
links=0
for source in (ROOT/"README.md",ROOT/"AUDIT.md",*(ROOT/"docs").glob("*.md")):
    text=source.read_text(encoding="utf-8")
    assert "C:/Users/" not in text and "C:\\Users\\" not in text,source
    assert text.count("$$")%2==0,source
    prose=re.sub(r"\$\$.*?\$\$|\$[^$\n]+\$","",text,flags=re.S)
    for target in re.findall(r"\[[^\]\n]*\]\(([^)]+)\)",prose):
        if "://" in target or target.startswith(("#","mailto:")):continue
        path=unquote(target.split("#",1)[0])
        assert (source.parent/path).exists(),(source,target)
        links+=1
for p in (ROOT/"verification/qa").glob("*checks.json"):
    assert json.loads(p.read_text(encoding="utf-8"))["result"]=="passed",p
review=json.loads((ROOT/"verification/qa/pdf_review.json").read_text(encoding="utf-8"))
for key in ("proof","proof-en","guide"):
    assert review[key]["visual_review"]=="passed"
    assert review[key]["visually_reviewed_pages"]==list(range(1,review[key]["pages"]+1))
    assert review[key]["rendered_pages"]==review[key]["pages"]
    pdf_data=(ROOT/review[key]["pdf"]).read_bytes()
    assert len(pdf_data)==review[key]["bytes"],("Stale PDF review size",key)
    assert hashlib.sha256(pdf_data).hexdigest()==review[key]["sha256"],("Stale PDF review hash",key)
print(json.dumps({"result":"passed","files":len(manifest["files"]),"local_links":links,
                  "pdf_pages":{key:review[key]["pages"] for key in ("proof","proof-en","guide")}}))

