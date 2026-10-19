"""Build the two Chinese PDFs.

Requires Pandoc and either Tectonic (XeTeX-based) or XeLaTeX.
Example:
  python tools/build_pdf.py --pandoc /path/to/pandoc --tectonic /path/to/tectonic
Set PDF_MAIN_FONT, PDF_BOLD_FONT, PDF_MONO_FONT to installed font names as needed.
Windows defaults: SimSun, SimHei, Consolas.
Optional --cache uses an existing Tectonic cache with --only-cached.
"""
from pathlib import Path
import argparse, os, re, shutil, subprocess, json

ROOT=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument("--pandoc",default=shutil.which("pandoc"))
parser.add_argument("--tectonic",default=shutil.which("tectonic"))
parser.add_argument("--xelatex",default=shutil.which("xelatex"))
parser.add_argument("--cache")
parser.add_argument("--only",choices=["proof","guide"])
args=parser.parse_args()
if not args.pandoc or not (args.tectonic or args.xelatex):
    parser.error("Pandoc and either Tectonic or XeLaTeX are required.")
out=ROOT/"output/pdf";out.mkdir(parents=True,exist_ok=True)
tmp=ROOT/"tmp/pdfs";tmp.mkdir(parents=True,exist_ok=True)
specs=[
 ("proof","paper.zh.md","Wormald竞赛图猜想1、2、6：Hessian恒等式与随机块模型",
  "Wormald猜想 - 完整证明",
  "独立研究稿，包含明确的原猜想对应、逐式证明、外部定理归属及发表前复核补充。推导由AI辅助完成，仍待独立数学审阅；有限检查不代替一般证明。"),
 ("guide","elementary-guide.zh.md","从微积分和线性代数理解Wormald竞赛图模型",
  "Wormald猜想 - 基础讲解",
  "配套基础讲解。以基本微积分和线性代数为起点，展开Hessian、Schur补、行列式、有理平方、随机期望及极限比较。一般研究结论仍待独立审阅。")
]
for key,name,title,short,subtitle in specs:
    if args.only and key!=args.only:continue
    text=(ROOT/"docs"/name).read_text(encoding="utf-8")
    body=text.split("\n",1)[1]
    for char in ("\u2010","\u2011","\u2012","\u2013","\u2014","\u2212"):
        body=body.replace(char,"-")
    md=tmp/(key+".md");md.write_text(body,encoding="utf-8")
    stem="wormald-conjectures-"+key+".zh"
    tex=tmp/(stem+".tex")
    cmd=[args.pandoc,str(md),"--from=markdown+tex_math_dollars+raw_tex-smart-superscript-subscript",
         "--to=latex","--standalone","--wrap=none","--syntax-highlighting=none",
         "--template="+str(ROOT/"tools/template.tex"),"-o",str(tex)]
    for k,v in {"title":title,"shorttitle":short,"subtitle":subtitle,
                "mainfont":os.environ.get("PDF_MAIN_FONT","SimSun"),
                "boldfont":os.environ.get("PDF_BOLD_FONT","SimHei"),
                "monofont":os.environ.get("PDF_MONO_FONT","Consolas")}.items():
        cmd.extend(["-V",k+"="+v])
    subprocess.run(cmd,check=True)
    rendered=tex.read_text(encoding="utf-8")
    rendered=re.sub(r"(?m)^(\\(?:sub)*section\*?\{)",r"\\Needspace{6\\baselineskip}\n\1",rendered)
    tex.write_text(rendered,encoding="utf-8")
    env=os.environ.copy()
    if args.cache:env["TECTONIC_CACHE_DIR"]=str(Path(args.cache).resolve())
    log=tmp/(key+"-console.txt")
    with log.open("w",encoding="utf-8") as stream:
        if args.tectonic:
            cmd=[args.tectonic,"--keep-logs","--keep-intermediates","--outdir",str(tmp)]
            if args.cache:cmd.append("--only-cached")
            subprocess.run(cmd+[str(tex)],check=True,env=env,stdout=stream,stderr=subprocess.STDOUT)
        else:
            for _ in range(3):
                subprocess.run([args.xelatex,"-interaction=nonstopmode","-halt-on-error",
                                "-output-directory="+str(tmp),str(tex)],check=True,
                               env=env,stdout=stream,stderr=subprocess.STDOUT)
    shutil.copy2(tmp/(stem+".pdf"),out/(stem+".pdf"))
    print(json.dumps({"pdf":str(out/(stem+".pdf"))},ensure_ascii=False),flush=True)

