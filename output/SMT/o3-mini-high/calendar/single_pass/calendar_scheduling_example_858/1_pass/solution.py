from z3 import *

# We represent days as integers:
# 0: Monday, 1: Tuesday, 2: Wednesday, 3: Thursday
day = Int('day')
s = Int('s')  # meeting start time in minutes since midnight

# Create an optimizer to incorporate a soft constraint (avoid Thursday for Carl)
opt = Optimize()

# Domain constraints:
# Meeting must be within work hours 9:00 (540 minutes) to 17:00 (1020 minutes)
opt.add(Or(day == 0, day == 1, day == 2, day == 3))
opt.add(s >= 540)
opt.add(s + 60 <= 1020)  # meeting duration is 60 minutes

# Busy intervals for each participant for each day (in minutes)
# Times are given as (start, end); meeting must NOT overlap these intervals.
# Note: It’s acceptable if the meeting ends exactly at a busy interval's start, or starts exactly at its end.
busy_intervals = {
    0: [  # Monday
        (660, 690),    # Carl: 11:00-11:30
        (540, 630),    # Margaret: 9:00-10:30
        (660, 1020)    # Margaret: 11:00-17:00
    ],
    1: [  # Tuesday
        (870, 900),    # Carl: 14:30-15:00
        (570, 720),    # Margaret: 9:30-12:00
        (810, 840),    # Margaret: 13:30-14:00
        (930, 1020)    # Margaret: 15:30-17:00
    ],
    2: [  # Wednesday
        (600, 690),    # Carl: 10:00-11:30
        (780, 810),    # Carl: 13:00-13:30
        (570, 720),    # Margaret: 9:30-12:00
        (750, 780),    # Margaret: 12:30-13:00
        (810, 870),    # Margaret: 13:30-14:30
        (900, 1020)    # Margaret: 15:00-17:00
    ],
    3: [  # Thursday
        (810, 840),    # Carl: 13:30-14:00
        (960, 990),    # Carl: 16:00-16:30
        (600, 720),    # Margaret: 10:00-12:00
        (750, 840),    # Margaret: 12:30-14:00
        (870, 1020)    # Margaret: 14:30-17:00
    ]
}

# For every busy interval on a given day, if the meeting is scheduled on that day,
# then it must not overlap the busy interval.
for d in [0, 1, 2, 3]:
    for (busy_start, busy_end) in busy_intervals[d]:
        opt.add(Or(day != d, s + 60 <= busy_start, s >= busy_end))

# Carl would like to avoid more meetings on Thursday.
# We add a soft constraint by minimizing a penalty if the meeting is on Thursday.
penalty = If(day == 3, 1, 0)
opt.minimize(penalty)

# Check for a solution:
if opt.check() == sat:
    model = opt.model()
    day_val = model[day].as_long()
    start_val = model[s].as_long()
    end_val = start_val + 60

    # Convert minutes to HH:MM format:
    start_hr = start_val // 60
    start_min = start_val % 60
    end_hr = end_val // 60
    end_min = end_val % 60

    # Map day integers to day names:
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday"}
    
    # The output must start with "SOLUTION:" followed by the day, start time and end time.
    print("SOLUTION:")
    print("Day: " + day_names[day_val])
    print("Start Time: {:02d}:{:02d}".format(start_hr, start_min))
    print("End Time: {:02d}:{:02d}".format(end_hr, end_min))
else:
    print("No solution found!")