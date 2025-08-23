#!/usr/bin/env python3

import subprocess
import re

lines = (
    subprocess.check_output(
        "rocq dep -f _CoqProject",
        shell=True,
    )
    .decode("utf-8")
    .split("\n")
)

processed_lines = []
for line in lines:
    line = line.replace("/", ".")
    line = re.sub(r"\.vo.*: [^ ]*\.v", "", line)
    line = re.sub(r"\.vo", "", line)
    processed_lines.append(line)
lines = processed_lines

with open("deps0.dot", "w") as f:
    f.write("digraph G {")
    f.write("rankdir=BT;")

    nodes = set()
    for l in lines:
        if "shiftreset" not in l:
            continue
        line = l.split(" ")
        src = line[0]
        dsts = line[1:]
        nodes.add(src)
        for d in dsts:
            nodes.add(d)
            f.write(f""""{src}" -> "{d}";""")

    for n in nodes:
        f.write(f""""{n}" [URL="{n}.html"];""")

    f.write("}")


subprocess.check_call("tred < deps0.dot > deps.dot", shell=True)
subprocess.check_call("dot -o deps.svg -Tsvg deps.dot", shell=True)

print("generated dependency svg")

with open("docs/shiftreset.preindex.html", "r") as f:
    preindex = f.read()

with open("deps.svg", "r") as f:
    svg = f.read()

index_file = "docs/shiftreset.index.html"
with open(index_file, "w") as f:
    f.write(re.sub(r"\$GRAPH", svg, preindex))

print(f"wrote {index_file}")
