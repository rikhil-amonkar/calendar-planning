from z3 import *

# Meeting parameters
DAY = "Monday"
WORK_START = 9 * 60      # 09:00 in minutes
WORK_END = 17 * 60       # 17:00 in minutes
DURATION = 30            # 30 minutes

# Busy intervals are represented as [start, end) in minutes since 00:00
busy_intervals = {
    "Bradley": [
        (9*60 + 30, 10*60),
        (12*60 + 30, 13*60),
        (13*60 + 30, 14*60),
        (15*60 + 30, 16*60),
    ],
    "Teresa": [
        (10*60 + 30, 11*60),
        (12*60, 12*60 + 30),
        (13*60, 13*60 + 30),
        (14*60 + 30, 15*60),
    ],
    "Elizabeth": [
        (9*60, 9*60 + 30),
        (10*60 + 30, 11*60 + 30),
        (13*60, 13*60 + 30),
        (14*60 + 30, 15*60),
        (15*60 + 30, 17*60),
    ],
    "Christian": [
        (9*60, 9*60 + 30),
        (10*60 + 30, 17*60),
    ],
}

# Z3 variables
start = Int('start')
end = Int('end')

s = Solver()
s.add(end == start + DURATION)
s.add(start >= WORK_START)
s.add(end <= WORK_END)

# Non-overlap constraints: [start, end) must not intersect any busy interval [b_start, b_end)
for person, intervals in busy_intervals.items():
    for b_start, b_end in intervals:
        s.add(Or(end <= b_start, start >= b_end))

# Solve
if s.check() != sat:
    raise RuntimeError("No feasible meeting time found, but a solution was expected.")

m = s.model()
start_min = m[start].as_long()
end_min = m[end].as_long()

def to_hhmm(total_minutes: int) -> str:
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

start_str = to_hhmm(start_min)
end_str = to_hhmm(end_min)

# Output format: Day {HH:MM:HH:MM}
print(f"{DAY} {{{start_str}:{end_str}}}")