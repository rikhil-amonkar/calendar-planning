from z3 import Optimize, Int, If, Or, sat

# Meeting parameters
duration = 60               # 60 minutes meeting
WORK_START = 9 * 60         # 9:00 in minutes (540)
WORK_END = 17 * 60          # 17:00 in minutes (1020)

# Map days 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Jesse's busy schedule (times in minutes after midnight)
jesse_busy = {
    1: [  # Tuesday
        (15 * 60 + 30, 16 * 60)  # 15:30 to 16:00
    ],
    2: [  # Wednesday
        (13 * 60, 13 * 60 + 30)  # 13:00 to 13:30
    ],
    3: [  # Thursday
        (16 * 60, 16 * 60 + 30)  # 16:00 to 16:30
    ],
    4: [  # Friday
        (12 * 60 + 30, 13 * 60)  # 12:30 to 13:00
    ]
}

# Terry's busy schedule
terry_busy = {
    0: [  # Monday
        (9 * 60, 9 * 60 + 30),    # 9:00 to 9:30 
        (10 * 60, 10 * 60 + 30),  # 10:00 to 10:30
        (11 * 60, 13 * 60),       # 11:00 to 13:00
        (13 * 60 + 30, 14 * 60 + 30),  # 13:30 to 14:30
        (16 * 60, 16 * 60 + 30)   # 16:00 to 16:30
    ],
    1: [  # Tuesday
        (9 * 60, 10 * 60),        # 9:00 to 10:00
        (10 * 60 + 30, 11 * 60 + 30),  # 10:30 to 11:30
        (12 * 60, 16 * 60 + 30)     # 12:00 to 16:30
    ],
    2: [  # Wednesday
        (9 * 60, 10 * 60),        # 9:00 to 10:00
        (10 * 60 + 30, 13 * 60),   # 10:30 to 13:00
        (13 * 60 + 30, 14 * 60),   # 13:30 to 14:00
        (14 * 60 + 30, 15 * 60),   # 14:30 to 15:00
        (15 * 60 + 30, 16 * 60 + 30)  # 15:30 to 16:30
    ],
    3: [  # Thursday
        (9 * 60 + 30, 11 * 60),    # 9:30 to 11:00
        (11 * 60 + 30, 12 * 60),   # 11:30 to 12:00
        (13 * 60, 14 * 60),        # 13:00 to 14:00
        (15 * 60 + 30, 17 * 60)     # 15:30 to 17:00
    ],
    4: [  # Friday
        (9 * 60, 10 * 60 + 30),    # 9:00 to 10:30
        (11 * 60, 16 * 60 + 30)    # 11:00 to 16:30
    ]
}

# Helper function to assert that a meeting starting at 'start' with 'duration'
# does not overlap a busy interval (busy_start, busy_end).
def no_overlap(start, duration, busy_start, busy_end):
    # Either meeting ends before the busy period, or starts after it.
    return Or(start + duration <= busy_start, start >= busy_end)

# Create the Z3 optimizer
opt = Optimize()

# Decision Variables:
# d: day of the meeting (0 to 4)
# s: start time (in minutes after midnight) of the meeting
d = Int("d")
s = Int("s")

# Meeting must be within work hours on any day.
opt.add(s >= WORK_START, s + duration <= WORK_END)
opt.add(d >= 0, d <= 4)

# Add busy schedule constraints for Jesse.
for day, intervals in jesse_busy.items():
    for (busy_start, busy_end) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Add busy schedule constraints for Terry.
for day, intervals in terry_busy.items():
    for (busy_start, busy_end) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Hard constraint based on Jesse's preference:
# Jesse cannot meet on Thursday after 14:00.
# That means if d==3 (Thursday) then the meeting must finish by 14:00.
opt.add(If(d == 3, s + duration <= 14 * 60, True))

# Soft preference for Terry: would rather not meet on Monday.
# We add a soft constraint minimizing a penalty if meeting is on Monday.
penalty = If(d == 0, 1, 0)
opt.minimize(penalty)

# Also, to schedule as early as possible (within those constraints) we add a secondary objective.
# We minimize (day*WORK_END + s) which prioritizes early day and early start time.
opt.minimize(d * WORK_END + s)

# Check for solution and print it.
if opt.check() == sat:
    model = opt.model()
    chosen_day = model[d].as_long()
    meeting_start = model[s].as_long()
    meeting_end = meeting_start + duration
    sh, sm = divmod(meeting_start, 60)
    eh, em = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
        day_names[chosen_day], sh, sm, eh, em))
else:
    print("No valid meeting time found.")