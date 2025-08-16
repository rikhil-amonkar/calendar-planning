from z3 import Optimize, Int, Or, And, sat

def minutes_to_str(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

# Working hours and meeting duration (in minutes)
WORK_START = 9 * 60   # 09:00 -> 540
WORK_END   = 17 * 60  # 17:00 -> 1020
DURATION = 30

# Busy intervals as (start_min, end_min) in absolute minutes from 00:00
busy = {
    "Andrea": [],  # wide open
    "Jack": [
        (9*60, 9*60 + 30),     # 09:00-09:30
        (14*60, 14*60 + 30),   # 14:00-14:30
    ],
    "Madison": [
        (9*60 + 30, 10*60 + 30),  # 09:30-10:30
        (13*60, 14*60),           # 13:00-14:00
        (15*60, 15*60 + 30),      # 15:00-15:30
        (16*60 + 30, 17*60),      # 16:30-17:00
    ],
    "Rachel": [
        (9*60 + 30, 10*60 + 30),  # 09:30-10:30
        (11*60, 11*60 + 30),      # 11:00-11:30
        (12*60, 13*60 + 30),      # 12:00-13:30
        (14*60 + 30, 15*60 + 30), # 14:30-15:30
        (16*60, 17*60),           # 16:00-17:00
    ],
    "Douglas": [
        (9*60, 11*60 + 30),       # 09:00-11:30
        (12*60, 16*60 + 30),      # 12:00-16:30
    ],
    "Ryan": [
        (9*60, 9*60 + 30),        # 09:00-09:30
        (13*60, 14*60),           # 13:00-14:00
        (14*60 + 30, 17*60),      # 14:30-17:00
    ]
}

# Z3 model: start is the meeting start time in absolute minutes from 00:00
start = Int('start')
opt = Optimize()

# Meeting must be within working hours
opt.add(And(start >= WORK_START, start + DURATION <= WORK_END))

# For each participant, ensure the meeting does not overlap any busy interval
for person, intervals in busy.items():
    for (b_start, b_end) in intervals:
        # Enforce non-overlap: [start, start+DURATION) lies entirely
        # before or after each busy interval [b_start, b_end)
        opt.add(Or(start + DURATION <= b_start, start >= b_end))

# Prefer the earliest feasible start time
opt.minimize(start)

if opt.check() == sat:
    model = opt.model()
    s_min = model[start].as_long()
    e_min = s_min + DURATION

    print("SOLUTION:")
    print("Day: Monday")
    print(f"Start Time: {minutes_to_str(s_min)} (24-hour format)")
    print(f"End Time: {minutes_to_str(e_min)} (24-hour format)")
else:
    print("No solution found.")