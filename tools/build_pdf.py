"""Build presentation-only PDFs from the newly downloaded upstream sources."""
from pathlib import Path
import argparse,subprocess,os,re,json
from pypdf import PdfReader
ROOT=Path(__file__).resolve().parents[1]
import shutil
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--pandoc',default=shutil.which('pandoc'))
parser.add_argument('--tectonic',default=shutil.which('tectonic'))
parser.add_argument('--xelatex',default=shutil.which('xelatex'))
parser.add_argument('--cache')
parser.add_argument('--output-dir',default='output/pdf')
parser.add_argument('--only',choices=['proof','proof-en','guide','complete-proof'])
args=parser.parse_args()
if not args.pandoc or not (args.tectonic or args.xelatex):
    parser.error('Pandoc and either Tectonic or XeLaTeX are required.')
PANDOC=args.pandoc
TECTONIC=args.tectonic
CACHE=Path(args.cache).resolve() if args.cache else None
OUT=(ROOT/args.output_dir).resolve();OUT.mkdir(parents=True,exist_ok=True)
TMP=ROOT/'tmp/pdfs';TMP.mkdir(parents=True,exist_ok=True)
PUBLIC={'paper.zh':('proof','wormald-conjectures-proof.zh.pdf'),
        'paper.en':('proof-en','wormald-conjectures-proof.en.pdf'),
        'guide.zh':('guide','wormald-conjectures-guide.zh.pdf'),
        'lean-guide.zh':('complete-proof','wormald-conjectures-complete-proof.zh.pdf')}
specs=[
 ("paper.zh","paper.zh.md","Wormald猜想 · 中文论文","刘星辰","2026年10月21日。公开研究稿，版本0.2.6。"),
 ("paper.en","paper.en.md","Wormald's conjectures · Research manuscript","Xingchen Liu","21 October 2026. Public research manuscript, version 0.2.6."),
 ("guide.zh","elementary-guide.zh.md","Wormald猜想 · 基础讲解","刘星辰","2026年10月21日，公开研究稿的配套基础讲解。"),
 ("lean-guide.zh","concise-complete-proof.zh.md","Wormald猜想 · 完整证明导读","",""),
]
report_path=ROOT/"verification/qa/pdf_build.json"
reports=json.loads(report_path.read_text(encoding="utf-8")) if report_path.exists() else {}
for key,name,short,author,date in specs:
    if args.only and PUBLIC[key][0]!=args.only:continue
    source=(ROOT/"docs"/name).read_text(encoding="utf-8")
    title,body=source.split("\n",1);title=title.lstrip("# ").strip();body=body.lstrip()
    paragraphs=body.split("\n\n")
    if paragraphs[0].strip() in {"刘星辰","Xingchen Liu"}:paragraphs=paragraphs[2:]
    elif paragraphs[0].startswith("刘星辰。"):paragraphs=paragraphs[1:]
    body="\n\n".join(paragraphs)
    # The math and prose are untouched; remove layout-sensitive Unicode hyphens in rendering only.
    for char in ("\u2010","\u2011","\u2012","\u2013","\u2014","\u2212"):
        body=body.replace(char,"-")
    md=TMP/(key+".md");md.write_text(body,encoding="utf-8")
    tex=TMP/(key+".tex")
    english=key=="paper.en"
    variables={
        "title":title,"shorttitle":short,"author":author,"date":date,
        "locale":"en" if english else "zh","contents":"Contents" if english else "目录",
        "runningdate":"2026-10-21" if key!="lean-guide.zh" else "",
        "subject":"Presentation-only edition; upstream commit 29de4fbb8586d8d7c116b7ed1733510ee0e324a1",
        "definitionname":"Definition" if english else "定义",
        "theoremname":"Theorem" if english else "定理",
        "lemmaname":"Lemma" if english else "引理",
        "corollaryname":"Corollary" if english else "推论",
        "externalname":"Quoted theorem" if english else "引用定理",
        "examplename":"Example" if english else "例",
        "proofname":"Proof" if english else "证明",
    }
    cmd=[str(PANDOC),str(md),"--from=markdown+fenced_divs+tex_math_dollars+tex_math_single_backslash+raw_tex-smart-superscript-subscript",
         "--to=latex","--standalone","--wrap=none","--syntax-highlighting=none",
         "--lua-filter="+str(ROOT/"tools/structure.lua"),"--template="+str(ROOT/"tools/template.tex"),"-o",str(tex)]
    for k,v in variables.items():cmd.extend(["-V",k+"="+v])
    if english:cmd.extend(["-V","english=true"])
    if key=="guide.zh":cmd.extend(["-V","showtoc=true","-V","compactguide=true"])
    subprocess.run(cmd,check=True)
    rendered=tex.read_text(encoding="utf-8")
    rendered=re.sub(r"(?m)^(\\section\*?\{)",r"\\Needspace{8\\baselineskip}\n\1",rendered)
    rendered=re.sub(r"(?m)^(\\subsection\*?\{)",r"\\Needspace{5\\baselineskip}\n\1",rendered)
    rendered=re.sub(r"(?m)^(\\begin\{(?:definition|theorem|lemma|corollary|externaltheorem|example)\})",
                    r"\\Needspace{4\\baselineskip}\n\1",rendered)
    rendered=re.sub(r"(?m)^(\\begin\{structuredproof\})",
                    r"\\Needspace{5\\baselineskip}\n\1",rendered)
    # Keep a short display introduction (e.g. "Let" or "设") with its formula.
    chunks=re.split(r"(\\\[.*?\\\])",rendered,flags=re.S)
    for i in range(0,len(chunks)-1,2):
        match=re.search(r"(?:^|\n\n)([^\n]+)\n\n$",chunks[i])
        if not match:continue
        intro=match.group(1)
        visible=re.sub(r"\\\(.*?\\\)","x",intro)
        before=chunks[i][:match.start(1)]
        first_in_environment=bool(re.search(r"\\begin\{[a-z]+\}(?:\[[^\n]*\]|\{[^\n]*\})?\n\n$",before))
        if not intro.startswith("\\") and len(visible)<=48 and not first_in_environment:
            start=match.start(1)
            chunks[i]=chunks[i][:start]+r"\Needspace{3\baselineskip}"+"\n"+chunks[i][start:]
    rendered="".join(chunks)
    if english:
        for intro in ("Since","It follows that"):
            rendered=rendered.replace("\n"+intro+"\n","\n"+r"\Needspace{5\baselineskip}"+"\n"+intro+"\n")
    references=r"\subsection{References}" if english else r"\subsection{参考文献}"
    if references in rendered:
        rendered=rendered.replace(references,r"\begingroup\small\linespread{1}\selectfont"+"\n"+references)
        rendered=rendered.replace(r"\end{document}",r"\endgroup"+"\n"+r"\end{document}")
    tex.write_text(rendered,encoding="utf-8")
    env=os.environ.copy()
    if CACHE:env["TECTONIC_CACHE_DIR"]=str(CACHE)
    console=TMP/(key+"-console.txt")
    with console.open("w",encoding="utf-8") as stream:
        if TECTONIC:
            command=[str(TECTONIC),'--keep-logs','--keep-intermediates','--outdir',str(TMP)]
            if CACHE:command.append('--only-cached')
            subprocess.run(command+[str(tex)],env=env,stdout=stream,stderr=subprocess.STDOUT,check=True)
        else:
            for _ in range(3):
                subprocess.run([args.xelatex,'-interaction=nonstopmode','-halt-on-error',
                                '-output-directory='+str(TMP),str(tex)],
                               env=env,stdout=stream,stderr=subprocess.STDOUT,check=True)
    pdf=OUT/PUBLIC[key][1];pdf.write_bytes((TMP/(key+".pdf")).read_bytes())
    log=(TMP/(key+".log")).read_text(encoding="utf-8",errors="replace")
    warnings=[line for line in log.splitlines() if re.search(
        r"Overfull|Missing character|undefined reference|Undefined control|LaTeX Error|headheight is too small",line,re.I)]
    reports[key]={"pdf":str(pdf.relative_to(ROOT)).replace("\\","/"),"pages":len(PdfReader(pdf).pages),
                  "critical_layout_warnings":warnings,"source":name}
    print(json.dumps({key:reports[key]},ensure_ascii=False),flush=True)
report_path.write_text(json.dumps(reports,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
