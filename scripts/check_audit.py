#!/usr/bin/env python3
"""Fail closed on forbidden proof shortcuts, missing imports, or unaudited theorems."""

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def lean_code(text):
    """Erase nested comments and strings, preserving line positions."""
    out = []
    i = depth = 0
    string = False
    while i < len(text):
        pair = text[i:i + 2]
        ch = text[i]
        if depth:
            if pair == "/-":
                depth += 1
                out.extend("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
        elif string:
            if ch == "\\":
                out.extend("  ")
                i += 2
            else:
                string = ch != '"'
                out.append("\n" if ch == "\n" else " ")
                i += 1
        elif pair == "/-":
            depth = 1
            out.extend("  ")
            i += 2
        elif pair == "--":
            end = text.find("\n", i)
            end = len(text) if end == -1 else end
            out.extend(" " * (end - i))
            i = end
        elif ch == '"':
            string = True
            out.append(" ")
            i += 1
        else:
            out.append(ch)
            i += 1
    if depth or string:
        raise ValueError("Unterminated Lean comment or string")
    return "".join(out)


def check():
    paths = [ROOT / "Ginibre.lean", ROOT / "Audit.lean"] + sorted((ROOT / "Ginibre").rglob("*.lean"))
    code = {p: lean_code(p.read_text()) for p in paths}
    errors = []
    for path, text in code.items():
        bad = re.search(r"\b(?:sorry|admit|unsafe|axiom|native_decide|set_option)\b", text)
        if bad:
            errors.append(f"Forbidden construct in {path.relative_to(ROOT)}: {bad.group()}")

    theorems = set()
    modules = {}
    for path in paths[2:]:
        text = code[path]
        namespaces = re.findall(r"^namespace\s+(\S+)", text, re.M)
        if namespaces != ["Ginibre"]:
            errors.append(f"Unexpected namespace layout in {path.relative_to(ROOT)}")
        names = re.findall(r"\b(?:theorem|lemma)\s+([^\s{(:]+)", text)
        theorems.update("Ginibre." + name for name in names)
        modules[".".join(path.relative_to(ROOT).with_suffix("").parts)] = path

    audits = re.findall(r"^#print axioms\s+(\S+)", code[ROOT / "Audit.lean"], re.M)
    if len(audits) != len(set(audits)):
        errors.append("Duplicate #print axioms commands")
    if theorems != set(audits):
        errors.append(f"Missing audits: {sorted(theorems - set(audits))}")
        errors.append(f"Unexpected audits: {sorted(set(audits) - theorems)}")

    seen = set()
    pending = [ROOT / "Ginibre.lean"]
    while pending:
        path = pending.pop()
        for name in re.findall(r"^import\s+(Ginibre\.\S+)", code[path], re.M):
            if name not in modules:
                errors.append(f"Missing authored import: {name}")
            elif name not in seen:
                seen.add(name)
                pending.append(modules[name])
    if seen != set(modules):
        errors.append(f"Outside root import closure: {sorted(set(modules) - seen)}")

    if len(sys.argv) > 1:
        log = Path(sys.argv[1]).read_text()
        results = {}
        for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log):
            if name in results:
                errors.append(f"Duplicate audit result: {name}")
            results[name] = {a.strip() for a in axioms.split(",") if a.strip()}
        for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
            if name in results:
                errors.append(f"Duplicate audit result: {name}")
            results[name] = set()
        if set(results) != theorems:
            errors.append(f"Audit log missing: {sorted(theorems - set(results))}")
            errors.append(f"Audit log extra: {sorted(set(results) - theorems)}")
        for name, axioms in results.items():
            if axioms - ALLOWED:
                errors.append(f"Disallowed axioms for {name}: {sorted(axioms - ALLOWED)}")
        if re.search(r"(^|\n).*\berror:", log):
            errors.append("Lean error in audit log")

    if errors:
        raise SystemExit("\n".join(errors))
    print(f"PASS: {len(modules)} modules, {len(theorems)} theorems; complete root/audit coverage.")
    if len(sys.argv) > 1:
        print("PASS: only propext, Classical.choice, and Quot.sound in audit results.")


if __name__ == "__main__":
    check()
