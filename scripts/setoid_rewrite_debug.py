# https://github.com/rocq-prover/rocq/issues/6141#issuecomment-345758104

import argparse
import re
import sys


def process_log(log):
    debugs = find_debugs(log)

    print(debugs)

    proper_subrelations = []
    for i, l in enumerate(debugs):
        if "proper_subrelation" in l:
            proper_subrelations.append(i)

    instance_candidates = []
    for i in proper_subrelations:
        prev_line = debugs[i - 1]
        if "looking for" in prev_line:
            inst = re.match(r"[^(]*\((.*)\)[^)]*", prev_line).group(1)
            inst = re.sub(r"\?\w+", "eq", inst)
            flip_count = inst.count("flip")
            instance_candidates.append(
                (
                    f"""#[global]
Instance aaa:
  {inst}.
Proof.
Admitted.""",
                    flip_count,
                )
            )

    # Sort instance_candidates by flip_count in ascending order
    instance_candidates.sort(key=lambda x: x[1])

    # Print sorted instances
    for instance, _ in instance_candidates:
        print(instance)
        print()


# Get all the debug lines out of the file
def find_debugs(log):
    debugs = []
    cur_line = ""

    for line in log:
        line = line.replace("\r", "").replace("\n", "")
        if line.startswith("Debug:"):
            if cur_line:
                debugs.append(cur_line)
            cur_line = line
        else:
            if cur_line:
                cur_line += " " + line.strip()
    debugs.append(cur_line)
    return debugs


def main():
    # parser = argparse.ArgumentParser()
    # parser.add_argument("-f", "--filename", required=True)
    # args = parser.parse_args()
    # with open(args.filename) as f:
    #     log = f.readlines()
    log = sys.stdin.readlines()
    process_log(log)


if __name__ == "__main__":
    main()
