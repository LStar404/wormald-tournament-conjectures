"""Check published file hashes, local Markdown links and check-record status."""
from pathlib import Path
from urllib.parse import unquote
import hashlib,json,re

ROOT=Path(__file__).resolve().parents[1]
manifest=json.loads((ROOT/"MANIFEST.json").read_text(encoding="utf-8"))
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
        if "://" in target or target.startswith("#"):continue
        path=unquote(target.split("#",1)[0])
        assert (source.parent/path).is_file(),(source,target)
        links+=1
for p in (ROOT/"verification/qa").glob("*checks.json"):
    assert json.loads(p.read_text(encoding="utf-8"))["result"]=="passed",p
review=json.loads((ROOT/"verification/qa/pdf_review.json").read_text(encoding="utf-8"))
for key in ("proof","guide"):
    assert review[key]["visual_review"]=="passed"
    assert review[key]["visually_reviewed_pages"]==list(range(1,review[key]["pages"]+1))
print(json.dumps({"result":"passed","files":len(manifest["files"]),"local_links":links,
                  "pdf_pages":[review["proof"]["pages"],review["guide"]["pages"]]}))

