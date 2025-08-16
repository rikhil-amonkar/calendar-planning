from z3 import Solver, Int, Or

def minutes(h, m):
    return h * 60 + m

def fmt_time(m):
    hh = m // 60
    mm = m % 60
    return f"{hh:02d}:{mm:02d}"

# Meeting parameters
WORK_START = minutes(9, 0)
WORK_END = minutes(17, 0)
MEETING_DURATION = 30  # minutes

# Busy intervals (start, end) in minutes from midnight
busy_schedules = {
    "Diane": [
        (minutes(9, 30), minutes(10, 0)),
        (minutes(14, 30), minutes(15, 0)),
    ],
    "Jack": [
        (minutes(13, 30), minutes(14, 0)),
        (minutes(14, 30), minutes(15, 0)),
    ],
    "Eugene": [
        (minutes(9, 0), minutes(10, 0)),
        (minutes(10, 30), minutes(11, 30)),
        (minutes(12, 0), minutes(14, 30)),
        (minutes(15, 0), minutes(16, 30)),
    ],
    "Patricia": [
        (minutes(9, 30), minutes(10, 30)),
        (minutes(11, 0), minutes(12, 0)),
        (minutes(12, 30), minutes(14, 0)),
        (minutes(15, 0), minutes(16, 30)),
    ],
}

# Z3 variables
start = Int("start")
end = Int("end")

s = Solver()

# Duration and work hours constraints
s.add(end - start == MEETING_DURATION)
s.add(start >= WORK_START, end <= WORK_END)

# Avoid all busy intervals for each participant
for participant, intervals in busy_schedules.items():
    for (b_start, b_end) in intervals:
        s.add(Or(end <= b_start, start >= b_end))

if s.check() == 1:  # sat
    m = s.model()
    st = m[start].as_long()
    en = m[end].as_long()
    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {fmt_time(st)} (24-hour format)")
    print(f"End Time: {fmt_time(en)} (24-hour format)")
else:
    print("No solution found.")