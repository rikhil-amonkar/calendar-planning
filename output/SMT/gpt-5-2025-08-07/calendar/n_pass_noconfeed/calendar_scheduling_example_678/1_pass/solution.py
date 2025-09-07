from z3 import *

def to_hhmm(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

# Variables
day = Int('day')          # 0 = Monday, 1 = Tuesday
start = Int('start')      # minutes from 00:00 within the chosen day
dur = IntVal(60)          # meeting duration in minutes

s = Optimize()

# Day domain
s.add(Or(day == 0, day == 1))

# Work hours: 09:00 to 17:00
s.add(start >= 9*60)          # >= 540
s.add(start + dur <= 17*60)   # <= 1020

# Helper: prevent overlap with a busy interval when on a given day
def no_overlap(d, bstart, bend):
    # Not (day == d AND overlap)
    s.add(Not(And(day == d, start < bend, start + dur > bstart)))

# Busy schedules (minutes from midnight)
# Russell:
#   Monday: 10:30-11:00
no_overlap(0, 10*60 + 30, 11*60)
#   Tuesday: 13:00-13:30
no_overlap(1, 13*60, 13*60 + 30)

# Alexander:
#   Monday: 9:00-11:30, 12:00-14:30, 15:00-17:00
no_overlap(0, 9*60, 11*60 + 30)
no_overlap(0, 12*60, 14*60 + 30)
no_overlap(0, 15*60, 17*60)
#   Tuesday: 9:00-10:00, 13:00-14:00, 15:00-15:30, 16:00-16:30
no_overlap(1, 9*60, 10*60)
no_overlap(1, 13*60, 14*60)
no_overlap(1, 15*60, 15*60 + 30)
no_overlap(1, 16*60, 16*60 + 30)

# Preference: Russell would rather not meet on Tuesday before 13:30 (treat as constraint)
s.add(Implies(day == 1, start >= 13*60 + 30))

# Optional: find the earliest feasible time
s.minimize(day)   # prefer Monday if possible (not possible here)
s.minimize(start) # earliest time within the chosen day

if s.check() == sat:
    m = s.model()
    d = m[day].as_long()
    st = m[start].as_long()
    en = st + 60
    day_str = "Monday" if d == 0 else "Tuesday"
    print(f"{day_str} {{{to_hhmm(st)}:{to_hhmm(en)}}}")
else:
    print("No feasible meeting time found.")