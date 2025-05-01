from z3 import *

# ──────────────────────────────────────────────────────────────────────────────
# Canonical scalars
MINUTES   = lambda h, m=0: 60*h + m            # helper → minutes since 00:00
DAYS      = ["Mon", "Tue", "Wed", "Thu", "Fri"]
BUS_START = MINUTES(9)                         # 09:00
BUS_END   = MINUTES(17)                        # 17:00
DURATION  = 30                                 # meeting length (minutes)

# ──────────────────────────────────────────────────────────────────────────────
# Decision variables
d  = Int("day_index")                          # 0 = Mon … 4 = Fri
ts = Int("start_min")                          # minutes since 00:00, same day

# ──────────────────────────────────────────────────────────────────────────────
# Universal domain constraints
s   = Solver()                                 # can swap to Optimize later
s.add(d >= 0, d <= 4)
s.add(ts >= BUS_START, ts + DURATION <= BUS_END)

# ──────────────────────────────────────────────────────────────────────────────
# Hard constraints  (non-overlap with existing bookings)
def no_conflict(person, blocks):
    """
    Assert that a 30-minute slot [ts, ts+30) does not overlap
    any busy 'blocks' for the given 'person'.
    """
    for day_idx, intervals in blocks.items():
        for (b_start, b_end) in intervals:
            # Only apply on the matching day, else vacuously true
            s.add(Implies(
                d == day_idx,
                Or(ts + DURATION <= b_start,       # finishes before busy
                   ts >= b_end)                    # starts after busy
            ))

# Busy maps  (day_index → list[(start,end)]) --------------------------
james_busy = {
  0: [(MINUTES(9,30), MINUTES(10)),
      (MINUTES(10,30), MINUTES(11)),
      (MINUTES(15), MINUTES(15,30)),
      (MINUTES(16), MINUTES(16,30))],
  1: [(MINUTES(9), MINUTES(10)),
      (MINUTES(10,30), MINUTES(11)),
      (MINUTES(12), MINUTES(13)),
      (MINUTES(14), MINUTES(14,30)),
      (MINUTES(15,30), MINUTES(16,30))],
  2: [(MINUTES(10), MINUTES(11)),
      (MINUTES(15,30), MINUTES(16)),
      (MINUTES(16,30), MINUTES(17))],
  4: [(MINUTES(10), MINUTES(10,30)),
      (MINUTES(13), MINUTES(14)),
      (MINUTES(14,30), MINUTES(15))]
}

betty_busy = {
  0: [(MINUTES(10,30), MINUTES(13)),
      (MINUTES(13,30), MINUTES(14,30)),
      (MINUTES(15), MINUTES(17))],
  1: [(MINUTES(9), MINUTES(16,30))],
  2: [(MINUTES(9), MINUTES(12,30)),
      (MINUTES(13), MINUTES(13,30)),
      (MINUTES(14,30), MINUTES(16,30))],
  3: [(MINUTES(9), MINUTES(9,30)),
      (MINUTES(10,30), MINUTES(11)),
      (MINUTES(11,30), MINUTES(13)),
      (MINUTES(13,30), MINUTES(15)),
      (MINUTES(15,30), MINUTES(17))],
  4: [(MINUTES(9), MINUTES(9,30)),
      (MINUTES(11,30), MINUTES(12)),
      (MINUTES(13,30), MINUTES(16))]
}

no_conflict("James",  james_busy)
no_conflict("Betty",  betty_busy)

# ──────────────────────────────────────────────────────────────────────────────
# Soft preference  (Betty dislikes Wed & Fri → minimise violation cost)
opt = Optimize()
opt.add(s.assertions())                        # import hard constraints

PENALTY = 1000                                 # large cost to discourage pick
soft = And(d != 2, d != 4)                     # True → zero cost; False → cost
opt.add_soft(soft, weight=PENALTY, id="Betty_pref")

# Objective: earliest chronological slot (lexicographic)
# Lower = earlier ⇒ minimise (day_index * 10000 + start_min)
priority = d*10000 + ts
h = opt.minimize(priority)

# ──────────────────────────────────────────────────────────────────────────────
# Solve
if opt.check() == sat:
    m   = opt.model()
    day = DAYS[m[d].as_long()]
    beg = m[ts].as_long()
    hr  = beg // 60
    mn  = beg % 60
    print(f"Earliest viable slot: {day} {hr:02d}:{mn:02d}–{hr:02d}:{mn+30:02d}")
else:
    print("UNSAT – input spec contradicts itself (should not happen).")