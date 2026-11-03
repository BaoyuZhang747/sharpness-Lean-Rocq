"""Verify the distributed proof sources against their frozen-source identities.

Uses only Python's standard library. Does not run Lean, Rocq, or network commands.
"""
from pathlib import Path, PurePosixPath
import hashlib
import json
import sys


def main():
    root = Path(__file__).resolve().parents[1]
    manifest = json.loads((root / "SOURCE_MANIFEST.json").read_text(encoding="utf-8"))
    if manifest.get("schema") != "sharpness-source-manifest-v1":
        raise ValueError("Unrecognised source manifest schema")
    failures = []
    expected = set()
    proof_count = 0
    for item in manifest["files"]:
        relative = PurePosixPath(item["path"])
        if relative.is_absolute() or ".." in relative.parts or "\\" in item["path"]:
            raise ValueError(f"Invalid manifest path: {relative}")
        name = relative.as_posix()
        if name in expected:
            raise ValueError(f"Duplicate manifest path: {name}")
        expected.add(name)
        path = root.joinpath(*relative.parts)
        if path.is_symlink() or not path.is_file():
            failures.append(f"Missing or non-regular file: {name}")
            continue
        data = path.read_bytes()
        if len(data) != item["bytes"] or hashlib.sha256(data).hexdigest() != item["sha256"]:
            failures.append(f"Changed bytes: {name}")
        proof_count += item["kind"] == "proof-source"
    proof_expected = {item["path"] for item in manifest["files"] if item["kind"] == "proof-source"}
    proof_actual = {
        path.relative_to(root).as_posix()
        for folder, suffix in [(root / "lean" / "Sharpness", ".lean"), (root / "rocq", ".v")]
        for path in folder.rglob("*" ) if path.is_file() and path.suffix == suffix
    }
    for name in sorted(proof_actual - proof_expected):
        failures.append(f"Unlisted proof source: {name}")
    if failures:
        print("Source identity check FAILED:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1
    print(f"PASS: {proof_count} proof sources and {len(expected) - proof_count} toolchain records match SOURCE_MANIFEST.json.")
    print("This verifies file identities only; it does not compile or kernel-check proofs.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
