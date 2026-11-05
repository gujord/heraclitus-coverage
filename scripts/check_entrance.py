"""Check Appendix C's explicit finite prefix directly from the greedy rule."""
import json
from pathlib import Path

PREFIX = [1,2,-1,-2,-3,-4,-5,5,4,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,
          20,21,22,23,24,25,26,27,28,29,30,31,32,-32,-22,-12,-9,-6,-7,-8,-11,-10,
          -13,-14,-15,-16,-17,-18,-19,-20,-21,-24,-23,-26,-25,-28,-27,-30,-29,35,
          -33,-34,-31,33,34,37,-35,-36]


def allowed(d):
    return d in (1, 3, 10) or (d >= 64 and d % 4 == 0)


def check(prefix):
    used, current, snapshots = {0}, 0, {}
    for n, winner in enumerate(prefix, 1):
        if winner in used or not allowed(abs(winner-current)):
            raise ValueError('Repeated or unreachable destination')
        key = lambda z: (abs(z), z < 0)
        for z in range(-abs(winner), abs(winner)+1):
            if z not in used and key(z) < key(winner) and allowed(abs(z-current)):
                raise ValueError('Better unused destination')
        used.add(winner)
        current = winner
        snapshots[n] = (current, set(used))
    return snapshots


def main():
    s = check(PREFIX)
    expected = {64: (35, (set(range(-32,33)) - {-31}) | {35}),
                68: (33, set(range(-34,34)) | {35}),
                72: (-36, set(range(-36,36)) | {37})}
    if len(PREFIX) != 72 or any(s[n] != state for n, state in expected.items()):
        raise ValueError('Wrong entrance state')
    rejected = 0
    for bad in [[-1] + PREFIX[1:], PREFIX[:10] + [0] + PREFIX[11:], PREFIX[:64] + [-31] + PREFIX[65:]]:
        try:
            check(bad)
        except ValueError:
            rejected += 1
    if rejected != 3:
        raise ValueError('Damaged entrance accepted')
    report = {'status': 'PASS', 'moves': 72, 'exact_states': [64,68,72], 'rejections': rejected,
              'scope': 'Finite prefix only; universal transition and coverage proved in Lean and the paper.'}
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
