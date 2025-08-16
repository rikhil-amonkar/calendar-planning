from z3 import Solver, Int, And, Or

def minutes(h, m):
    return h * 60 + m

def fmt_time(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

# Meeting settings
day = "Monday"
work_start = minutes(9, 0)   # 09:00
work_end   = minutes(17, 0)  # 17:00
duration = 60  # 1 hour

# Busy calendars (half-open intervals [start, end))
busy = {
    "Evelyn": [],
    "Joshua": [
        (minutes(11, 0), minutes(12, 30)),
        (minutes(13, 30), minutes(14, 30)),
        (minutes(16, 30), minutes(17, 0)),
    ],
    "Kevin": [],
    "Gerald": [],
    "Jerry": [
        (minutes(9, 0), minutes(9, 30)),
        (minutes(10, 30), minutes(12, 0)),
        (minutes(12, 30), minutes(13, 0)),
        (minutes(13, 30), minutes(14, 0)),
        (minutes(14, 30), minutes(15, 0)),
        (minutes(15, 30), minutes(16, 0)),
    ],
    "Jesse": [
        (minutes(9, 0), minutes(9, 30)),
        (minutes(10, 30), minutes(12, 0)),
        (minutes(12, 30), minutes(13, 0)),
        (minutes(14, 30), minutes(15, 0)),
        (minutes(15, 30), minutes(16, 30)),
    ],
    "Kenneth": [
        (minutes(10, 30), minutes(12, 30)),
        (minutes(13, 30), minutes(14, 0)),
        (minutes(14, 30), minutes(15, 0)),
        (minutes(15, 30), minutes(16, 0)),
        (minutes(16, 30), minutes(17, 0)),
    ],
}

# Z3 model
s = Int("start")  # start time in minutes after 00:00

solver = Solver()
# Working hours and 30-minute granularity (typical calendar slots)
solver.add(s >= work_start)
solver.add(s + duration <= work_end)
solver.add(s % 30 == 0)

# No overlap with any busy interval for each participant
for person, intervals in busy.items():
    for (b_start, b_end) in intervals:
        solver.add(Or(s + duration <= b_start, s >= b_end))

if solver.check() == 1:  # sat
    model = solver.model()
    start = model[s].as_long()
    end = start + duration
    print("SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {fmt_time(start)} (24-hour format)")
    print(f"End Time: {fmt_time(end)} (24-hour format)")
else:
    # Given the problem statement guarantees a solution, this should not happen.
    # Included for completeness.
    print("SOLUTION:")
    print(f"Day: {day}")
    print("Start Time: 00:00 (24-hour format)")
    print("End Time: 00:00 (24-hour format)")