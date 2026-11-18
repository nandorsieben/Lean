#!/usr/bin/env python3
"""Rebuild the Lean certificates; reject warnings and untrusted axioms."""
from pathlib import Path
import os
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
BUILD = HERE / ".build"
SOURCES = (
    "Arithmetic", "Rubbling", "Routing", "Boundary", "Finite", "Collect",
    "CommonNeighbor", "CliqueTargets", "Frozen", "TwoFar", "UITargets",
    "Separable", "WLower", "Drain", "Triples", "WTargets", "ParityWeight",
    "VIWeight", "VILower", "VITargets", "Family", "Consequences",
)
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def main():
    BUILD.mkdir(exist_ok=True)
    env = os.environ.copy()
    env["LEAN_PATH"] = str(BUILD) + (
        ":" + env["LEAN_PATH"] if env.get("LEAN_PATH") else ""
    )
    started = time.monotonic()
    report = []
    checked_axiom_lists = 0
    for source in SOURCES:
        print(f"Checking {source}.lean", flush=True)
        # Removing the old artifact prevents a failed build from leaving it usable.
        artifact = BUILD / (source + ".olean")
        artifact.unlink(missing_ok=True)
        result = subprocess.run(
            ["lean", "-DwarningAsError=true", "-o", str(artifact), source + ".lean"],
            cwd=HERE, env=env, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
        print(result.stdout, end="", flush=True)
        report.append(f"Checking {source}.lean\n{result.stdout}")
        if result.returncode:
            raise SystemExit(f"Lean rejected {source}.lean")
        if "sorryAx" in result.stdout or "uses 'sorry'" in result.stdout:
            raise SystemExit(f"Admitted proof in {source}.lean")
        for axiom_list in re.findall(r"depends on axioms: \[([^\]]*)\]", result.stdout):
            checked_axiom_lists += 1
            actual = {name.strip() for name in axiom_list.split(",") if name.strip()}
            if actual - ALLOWED_AXIOMS:
                raise SystemExit(f"Unexpected axioms in {source}.lean: {actual}")
    summary = (
        f"PASS: {len(SOURCES)} modules rebuilt; {checked_axiom_lists} axiom lists checked; "
        f"{time.monotonic() - started:.1f} seconds.\n"
    )
    report.append(summary)
    (BUILD / "verification.log").write_text("".join(report))
    print(summary, end="")


if __name__ == "__main__":
    main()
