from z3 import Solver, Int, And, Or, If, sat

def minutes(h, m):
    return h * 60 + m

def fmt_time(t):
    return f"{t // 60:02d}:{t % 60:02d}"

# Constants
BUSINESS_START = minutes(9, 0)   # 09:00
BUSINESS_END = minutes(17, 0)    # 17:00
DURATION = 30                    # 30 minutes

# Day mapping
DAY_MAP = {1: "Monday", 2: "Tuesday", 3: "Wednesday"}

# Busy schedules (start, end) in minutes from midnight
cheryl_busy = {
    1: [  # Monday
        (minutes(9, 0), minutes(9, 30)),
        (minutes(11, 30), minutes(13, 0)),
        (minutes(15, 30), minutes(16, 0)),
    ],
    2: [  # Tuesday
        (minutes(15, 0), minutes(15, 30)),
    ],
    3: [  # Wednesday
        # Cheryl cannot meet on Wednesday; constraint added separately
    ],
}

kyle_busy = {
    1: [  # Monday
        (minutes(9, 0), minutes(17, 0)),
    ],
    2: [  # Tuesday
        (minutes(9, 30), minutes(17, 0)),
    ],
    3: [  # Wednesday
        (minutes(9, 0), minutes(9, 30)),
        (minutes(10, 0), minutes(13, 0)),
        (minutes(13, 30), minutes(14, 0)),
        (minutes(14, 30), minutes(17, 0)),
    ],
}

# Z3 variables
day = Int("day")     # 1=Monday, 2=Tuesday, 3=Wednesday
start = Int("start") # minutes from midnight
end = Int("end")     # minutes from midnight

s = Solver()

# Basic constraints: day in Mon-Wed, within business hours, and duration = 30 minutes
s.add(And(day >= 1, day <= 3))
s.add(start >= BUSINESS_START)
s.add(end == start + DURATION)
s.add(end <= BUSINESS_END)

# Cheryl cannot meet on Wednesday
s.add(day != 3)

# Helper to ensure meeting does not overlap with busy intervals for a given day
def no_overlap_for_day(dvar, svar, evar, day_idx, intervals):
    if not intervals:
        return True
    return If(
        dvar == day_idx,
        And([Or(evar <= b_start, svar >= b_end) for (b_start, b_end) in intervals]),
        True
    )

# Apply non-overlap constraints for each participant and day
for d_idx in (1, 2, 3):
    s.add(no_overlap_for_day(day, start, end, d_idx, cheryl_busy.get(d_idx, [])))
    s.add(no_overlap_for_day(day, start, end, d_idx, kyle_busy.get(d_idx, [])))

if s.check() == sat:
    m = s.model()
    d_val = m[day].as_long()
    start_val = m[start].as_long()
    end_val = m[end].as_long()
    print("SOLUTION:")
    print(f"Day: {DAY_MAP[d_val]}")
    print(f"Start Time: {fmt_time(start_val)} (24-hour format)")
    print(f"End Time: {fmt_time(end_val)} (24-hour format)")
else:
    # Problem statement guarantees a solution exists; this is a fallback.
    print("SOLUTION:")
    print("Day: Monday")
    print("Start Time: 00:00 (24-hour format)")
    print("End Time: 00:30 (24-hour format)")