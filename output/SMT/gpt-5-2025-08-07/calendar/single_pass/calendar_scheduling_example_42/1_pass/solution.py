from z3 import Solver, Int, Or, sat

def minutes(h, m):
    return h * 60 + m

def fmt(mins):
    return f"{mins // 60:02d}:{mins % 60:02d}"

# Problem setup
day = "Monday"
WORK_START = minutes(9, 0)
WORK_END = minutes(17, 0)
DURATION = 60  # minutes

# Busy intervals as [start, end) in minutes since 00:00
busy = {
    "Julie": [
        (minutes(9, 0), minutes(9, 30)),
        (minutes(11, 0), minutes(11, 30)),
        (minutes(12, 0), minutes(12, 30)),
        (minutes(13, 30), minutes(14, 0)),
        (minutes(16, 0), minutes(17, 0)),
    ],
    "Sean": [
        (minutes(9, 0), minutes(9, 30)),
        (minutes(13, 0), minutes(13, 30)),
        (minutes(15, 0), minutes(15, 30)),
        (minutes(16, 0), minutes(16, 30)),
    ],
    "Lori": [
        (minutes(10, 0), minutes(10, 30)),
        (minutes(11, 0), minutes(13, 0)),
        (minutes(15, 30), minutes(17, 0)),
    ],
}

# Z3 variables
Start = Int("Start")
End = Int("End")

# Solver and constraints
s = Solver()
s.add(Start >= WORK_START)
s.add(End == Start + DURATION)
s.add(End <= WORK_END)

# No overlap with any busy interval: For each [b_start, b_end), End <= b_start OR Start >= b_end
for person, intervals in busy.items():
    for b_start, b_end in intervals:
        s.add(Or(End <= b_start, Start >= b_end))

if s.check() == sat:
    m = s.model()
    start_val = m[Start].as_long()
    end_val = m[End].as_long()
    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {fmt(start_val)} (24-hour format)")
    print(f"End Time: {fmt(end_val)} (24-hour format)")
else:
    # Problem guarantees a solution exists, but handle just in case
    print("SOLUTION:")
    print(f"Day: {day}")
    print("Start Time: 00:00 (24-hour format)")
    print("End Time: 00:00 (24-hour format)")