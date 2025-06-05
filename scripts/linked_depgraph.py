#!/usr/bin/env python3

import subprocess
import re

lines = (
    subprocess.check_output(
        "coqdep -f _CoqProject",
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

print("digraph G {")
print("rankdir=BT;")

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
        print(f""""{src}" -> "{d}";""")

for n in nodes:
    print(f""""{n}" [URL="{n}.html"];""")


print("}")
