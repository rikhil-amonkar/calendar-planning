from z3 import *

def minutes_to_hhmm(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

# Constants
MONDAY, TUESDAY = 0, 1
work_start = 9 * 60      # 09:00
work_end = 17 * 60       # 17:00
duration = 30            # 30 minutes

# Z3 variables
Day = Int("Day")         # 0 = Monday, 1 = Tuesday
Start = Int("Start")
End = Int("End")

o = Optimize()

# Basic bounds and structure
o.add(Day >= MONDAY, Day <= TUESDAY)
o.add(Start >= work_start, Start <= work_end - duration)
o.add(End == Start + duration, End <= work_end)

# Optional: schedule on half-hour increments
o.add(Start % 30 == 0)

# Busy intervals per participant (day, start_min, end_min)
busy_intervals = []

# Jean busy: Tuesday 11:30-12:00, 16:00-16:30
busy_intervals += [
    (TUESDAY, 11*60 + 30, 12*60),
    (TUESDAY, 16*60, 16*60 + 30),
]

# Doris busy:
# Monday: 9:00-11:30, 12:00-12:30, 13:30-16:00, 16:30-17:00
busy_intervals += [
    (MONDAY, 9*60, 11*60 + 30),
    (MONDAY, 12*60, 12*60 + 30),
    (MONDAY, 13*60 + 30, 16*60),
    (MONDAY, 16*60 + 30, 17*60),
]
# Tuesday: 9:00-17:00
busy_intervals += [
    (TUESDAY, 9*60, 17*60),
]

# No-overlap constraints for each busy interval on its respective day
for d, b_start, b_end in busy_intervals:
    # If meeting is on day d, it must not overlap with [b_start, b_end)
    o.add(Implies(Day == d, Or(End <= b_start, Start >= b_end)))

# Preference: Doris would rather not meet on Monday after 14:00
# Model as minimizing a penalty if Monday and Start >= 14:00
penalty = If(And(Day == MONDAY, Start >= 14 * 60), 1, 0)

# Optimization objectives:
# 1) Minimize preference penalty
# 2) Prefer earlier day (Monday before Tuesday)
# 3) Prefer earliest possible start time
o.minimize(penalty)
o.minimize(Day)
o.minimize(Start)

if o.check() != sat:
    raise RuntimeError("No feasible schedule found.")

m = o.model()
day_val = m[Day].as_long()
start_val = m[Start].as_long()
end_val = m[End].as_long()

day_str = "Monday" if day_val == MONDAY else "Tuesday"

print("SOLUTION:")
print(f"Day: {day_str}")
print(f"Start Time: {minutes_to_hhmm(start_val)}")
print(f"End Time: {minutes_to_hhmm(end_val)}")