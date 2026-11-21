#!/usr/bin/env python3
"""Check that lean/ChallengeDefs.lean carries exactly the definition block of Challenge.lean.

Solution.lean takes its definitions from ChallengeDefs, and the comparator compares every
definition body of Challenge.lean against the one Solution.lean exports. This check makes
the copy visible to a reader: the block between `namespace M2Polymath` and the first theorem
docstring of Challenge.lean must equal the body of ChallengeDefs.lean's namespace.
"""
import sys
from pathlib import Path

root = Path(__file__).resolve().parent.parent
ch = (root / "Challenge.lean").read_text(encoding="utf-8")
cd = (root / "lean" / "ChallengeDefs.lean").read_text(encoding="utf-8")
ns = "namespace M2Polymath\n"
a = ch[ch.index(ns) + len(ns):ch.index("/-- **Exact degree, cheap nodes.**")].strip()
b = cd[cd.index(ns) + len(ns):cd.index("end M2Polymath")].strip()
if a != b:
    print("ChallengeDefs.lean differs from the definition block of Challenge.lean", file=sys.stderr)
    sys.exit(1)
print("ChallengeDefs.lean matches the definition block of Challenge.lean")
