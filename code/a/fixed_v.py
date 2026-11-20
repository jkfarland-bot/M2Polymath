"""M2a: side table. Least Z when the offset v is fixed in advance (not part of Theorem H).
Usage: python3 -I fixed_v.py"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from moments import feasible, nodes_for  # noqa: E402

for p in (2, 3, 5):
    for signed in (True, False):
        for v in (1, 2, 3):
            row = []
            for k in range(1, 5):
                Z = next((Z for Z in range(1, 41) if feasible(nodes_for(Z, signed), p, k, v, 'short')[0]), None)
                row.append(Z)
            print(f"p={p} {'signed' if signed else 'cheap '} v={v}: least Z for k=1..4: {row}")
# monotonicity in v: feasible at v implies feasible at v+1 (scale by p); spot check
bad = 0
for p in (2, 3, 5):
    for signed in (True, False):
        for k in (1, 2, 3):
            for Z in range(1, 16):
                fs = [feasible(nodes_for(Z, signed), p, k, v, 'short')[0] for v in range(0, 7)]
                if any(fs[i] and not fs[i + 1] for i in range(6)):
                    bad += 1
print("upward closure in v violations:", bad)
