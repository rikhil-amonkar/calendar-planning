from z3 import *

def minutes(h, m):
    return h * 60 + m

def minutes_to_hhmm(t):
    h = t // 60
    m = t % 60
    return f"{h:02d}:{m:02d}"

# Create solver
s = Solver()

# Meeting variables
start = Int('start')
end = Int('end')

# Constants
WORK_START = minutes(9, 0)    # 09:00
WORK_END = minutes(17, 0)     # 17:00
DURATION = 60                 # 1 hour
PAMELA_END_PREF = minutes(14, 30)  # Pamela does not want to meet after 14:30

# Basic constraints
s.add(start >= WORK_START)
s.add(end == start + DURATION)
s.add(end <= WORK_END)

# Pamela preference: meeting must not include any time after 14:30
s.add(end <= PAMELA_END_PREF)

# Busy schedules (half-open intervals [start, end))
busy = {
    "Anthony": [
        (minutes(9, 30), minutes(10, 0)),
        (minutes(12, 0), minutes(13, 0)),
        (minutes(16, 0), minutes(16, 30)),
    ],
    "Pamela": [
        (minutes(9, 30), minutes(10, 0)),
        (minutes(16, 30), minutes(17, 0)),
    ],
    "Zachary": [
        (minutes(9, 0), minutes(11, 30)),
        (minutes(12, 0), minutes(12, 30)),
        (minutes(13, 0), minutes(13, 30)),
        (minutes(14, 30), minutes(15, 0)),
        (minutes(16, 0), minutes(17, 0)),
    ]
}

# No overlap constraints: meeting [start, end) must not overlap any busy [bstart, bend)
def no_overlap(st, en, bstart, bend):
    return Or(en <= bstart, st >= bend)

for person, intervals in busy.items():
    for bstart, bend in intervals:
        s.add(no_overlap(start, end, bstart, bend))

# Solve
if s.check() == sat:
    m = s.model()
    start_time = m[start].as_long()
    end_time = m[end].as_long()
    output = (
        "SOLUTION:\n"
        f"Day: Monday\n"
        f"Start Time: {minutes_to_hhmm(start_time)}\n"
        f"End Time: {minutes_to_hhmm(end_time)}"
    )
    print(output)
else:
    # As per problem statement, a solution exists; this branch should not occur.
    # Provided for completeness.
    print("SOLUTION:\nDay: Monday\nStart Time: 00:00\nEnd Time: 00:00")