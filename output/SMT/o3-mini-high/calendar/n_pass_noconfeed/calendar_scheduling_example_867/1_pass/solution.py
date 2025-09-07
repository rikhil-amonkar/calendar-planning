from z3 import *

def minutes_to_str(m):
    hours = m // 60
    mins = m % 60
    return f"{hours:02d}:{mins:02d}"

# Meeting parameters
meeting_duration = 30
working_start = 9 * 60      # 9:00 in minutes
working_end = 17 * 60       # 17:00 in minutes
latest_start = working_end - meeting_duration

# Days encoding: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday
# Given the constraints:
# - Betty cannot meet on Monday.
# - Betty cannot meet on Tuesday or Thursday before 15:00 (15:00 = 900 minutes).
# - Scott would like to avoid more meetings on Wednesday.
# So we restrict the meeting to Tuesday (1) or Thursday (3).
d = Int('d')  # meeting day
s = Int('s')  # meeting start time in minutes

solver = Solver()

# Domain constraints for s and d.
solver.add(s >= working_start, s <= latest_start, s % 30 == 0)
solver.add(Or(d == 1, d == 3))  # Only Tuesday or Thursday allowed

# Betty's extra constraint: on Tuesday (1) or Thursday (3) she can meet only after 15:00.
solver.add(Implies(Or(d == 1, d == 3), s >= 15 * 60))

# Busy intervals for Betty and Scott.
# Each busy interval is a tuple: (day, busy_start, busy_end), where times are in minutes.
betty_busy = [
    # Monday (day=0) -- though Betty cannot meet Monday, we list them for completeness.
    (0, 10 * 60, 10 * 60 + 30),    # 10:00-10:30
    (0, 13 * 60 + 30, 14 * 60),      # 13:30-14:00
    (0, 15 * 60, 15 * 60 + 30),      # 15:00-15:30
    (0, 16 * 60, 16 * 60 + 30),      # 16:00-16:30

    # Tuesday (day=1)
    (1, 9 * 60, 9 * 60 + 30),        # 9:00-9:30
    (1, 11 * 60 + 30, 12 * 60),       # 11:30-12:00
    (1, 12 * 60 + 30, 13 * 60),       # 12:30-13:00
    (1, 13 * 60 + 30, 14 * 60),       # 13:30-14:00
    (1, 16 * 60 + 30, 17 * 60),       # 16:30-17:00

    # Wednesday (day=2)
    (2, 9 * 60 + 30, 10 * 60 + 30),   # 9:30-10:30
    (2, 13 * 60, 13 * 60 + 30),       # 13:00-13:30
    (2, 14 * 60, 14 * 60 + 30),       # 14:00-14:30

    # Thursday (day=3)
    (3, 9 * 60 + 30, 10 * 60),        # 9:30-10:00
    (3, 11 * 60 + 30, 12 * 60),       # 11:30-12:00
    (3, 14 * 60, 14 * 60 + 30),       # 14:00-14:30
    (3, 15 * 60, 15 * 60 + 30),       # 15:00-15:30
    (3, 16 * 60 + 30, 17 * 60)        # 16:30-17:00
]

scott_busy = [
    # Monday (day=0)
    (0, 9 * 60 + 30, 15 * 60),       # 9:30-15:00
    (0, 15 * 60 + 30, 16 * 60),      # 15:30-16:00
    (0, 16 * 60 + 30, 17 * 60),      # 16:30-17:00

    # Tuesday (day=1)
    (1, 9 * 60, 9 * 60 + 30),        # 9:00-9:30
    (1, 10 * 60, 11 * 60),           # 10:00-11:00
    (1, 11 * 60 + 30, 12 * 60),      # 11:30-12:00
    (1, 12 * 60 + 30, 13 * 60 + 30),  # 12:30-13:30
    (1, 14 * 60, 15 * 60),           # 14:00-15:00
    (1, 16 * 60, 16 * 60 + 30),      # 16:00-16:30

    # Wednesday (day=2)
    (2, 9 * 60 + 30, 12 * 60 + 30),  # 9:30-12:30
    (2, 13 * 60, 13 * 60 + 30),      # 13:00-13:30
    (2, 14 * 60, 14 * 60 + 30),      # 14:00-14:30
    (2, 15 * 60, 15 * 60 + 30),      # 15:00-15:30
    (2, 16 * 60, 16 * 60 + 30),      # 16:00-16:30

    # Thursday (day=3)
    (3, 9 * 60, 9 * 60 + 30),        # 9:00-9:30
    (3, 10 * 60, 10 * 60 + 30),      # 10:00-10:30
    (3, 11 * 60, 12 * 60),           # 11:00-12:00
    (3, 12 * 60 + 30, 13 * 60),      # 12:30-13:00
    (3, 15 * 60, 16 * 60),           # 15:00-16:00
    (3, 16 * 60 + 30, 17 * 60)       # 16:30-17:00
]

# For each busy interval, add the constraint that the meeting must not overlap.
# Two intervals [s, s+meeting_duration] and [busy_start, busy_end] do not overlap
# if s+meeting_duration <= busy_start or s >= busy_end.
for (day_val, busy_start, busy_end) in betty_busy:
    solver.add(Implies(d == day_val, Or(s + meeting_duration <= busy_start, s >= busy_end)))

for (day_val, busy_start, busy_end) in scott_busy:
    solver.add(Implies(d == day_val, Or(s + meeting_duration <= busy_start, s >= busy_end)))

# Attempt to solve the constraints.
if solver.check() == sat:
    m = solver.model()
    day_val = m[d].as_long()
    start = m[s].as_long()
    end = start + meeting_duration

    days = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    # Output the result in the format: Day HH:MM:HH:MM
    print(f"{days[day_val]} {minutes_to_str(start)}:{minutes_to_str(end)}")
else:
    print("No solution found.")