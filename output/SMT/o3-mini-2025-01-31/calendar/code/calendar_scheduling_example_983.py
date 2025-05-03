from z3 import Optimize, Int, If, Or, sat

# Meeting parameters
duration = 60               # Duration in minutes (1 hour)
WORK_START = 9 * 60         # 9:00 in minutes (540)
WORK_END = 17 * 60          # 17:00 in minutes (1020)

# Mapping days to numbers: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Jeffrey's busy schedule (times in minutes after midnight)
jeffrey_busy = {
    0: [  # Monday
        (11 * 60, 11 * 60 + 30),  # 11:00 to 11:30 --> 660 to 690
        (12 * 60 + 30, 13 * 60),  # 12:30 to 13:00 --> 750 to 780
        (14 * 60 + 30, 15 * 60)   # 14:30 to 15:00 --> 870 to 900
    ],
    1: [  # Tuesday
        (12 * 60 + 30, 13 * 60),  # 12:30 to 13:00 --> 750 to 780
        (14 * 60 + 30, 15 * 60)   # 14:30 to 15:00 --> 870 to 900
    ],
    2: [  # Wednesday
        (9 * 60 + 30, 10 * 60),   # 9:30 to 10:00 --> 570 to 600
        (10 * 60 + 30, 11 * 60),  # 10:30 to 11:00 --> 630 to 660
        (11 * 60 + 30, 12 * 60),  # 11:30 to 12:00 --> 690 to 720
        (13 * 60, 13 * 60 + 30),  # 13:00 to 13:30 --> 780 to 810
        (15 * 60, 15 * 60 + 30),  # 15:00 to 15:30 --> 900 to 930
        (16 * 60, 16 * 60 + 30)   # 16:00 to 16:30 --> 960 to 990
    ],
    3: [  # Thursday
        (11 * 60, 11 * 60 + 30),  # 11:00 to 11:30 --> 660 to 690
        (12 * 60 + 30, 13 * 60),  # 12:30 to 13:00 --> 750 to 780
        (15 * 60, 16 * 60),       # 15:00 to 16:00 --> 900 to 960
        (16 * 60 + 30, 17 * 60)   # 16:30 to 17:00 --> 990 to 1020
    ],
    4: [  # Friday
        (9 * 60 + 30, 10 * 60),   # 9:30 to 10:00 --> 570 to 600
        (12 * 60 + 30, 13 * 60 + 30),  # 12:30 to 13:30 --> 750 to 810
        (14 * 60 + 30, 15 * 60)   # 14:30 to 15:00 --> 870 to 900
    ]
}

# Timothy's busy schedule (times in minutes after midnight)
timothy_busy = {
    0: [  # Monday
        (9 * 60 + 30, 13 * 60),   # 9:30 to 13:00 --> 570 to 780
        (13 * 60 + 30, 16 * 60),  # 13:30 to 16:00 --> 810 to 960
        (16 * 60 + 30, 17 * 60)   # 16:30 to 17:00 --> 990 to 1020
    ],
    1: [  # Tuesday
        (9 * 60 + 30, 12 * 60),   # 9:30 to 12:00 --> 570 to 720
        (12 * 60 + 30, 14 * 60),  # 12:30 to 14:00 --> 750 to 840
        (14 * 60 + 30, 16 * 60),  # 14:30 to 16:00 --> 870 to 960
        (16 * 60 + 30, 17 * 60)   # 16:30 to 17:00 --> 990 to 1020
    ],
    2: [  # Wednesday
        (9 * 60 + 30, 10 * 60),   # 9:30 to 10:00 --> 570 to 600
        (10 * 60 + 30, 12 * 60 + 30),  # 10:30 to 12:30 --> 630 to 750
        (13 * 60, 16 * 60 + 30)   # 13:00 to 16:30 --> 780 to 990
    ],
    3: [  # Thursday
        (9 * 60, 9 * 60 + 30),    # 9:00 to 9:30 --> 540 to 570
        (10 * 60 + 30, 16 * 60)   # 10:30 to 16:00 --> 630 to 960
    ],
    4: [  # Friday
        (9 * 60, 11 * 60 + 30),   # 9:00 to 11:30 --> 540 to 690
        (12 * 60, 14 * 60),       # 12:00 to 14:00 --> 720 to 840
        (14 * 60 + 30, 16 * 60 + 30)  # 14:30 to 16:30 --> 870 to 990
    ]
}

# Helper function: ensures that a meeting starting at meet_start with duration meet_duration
# does not overlap with an interval (busy_start, busy_end)
def no_overlap(meet_start, meet_duration, busy_start, busy_end):
    return Or(meet_start + meet_duration <= busy_start, meet_start >= busy_end)

# Create the Z3 Optimizer
opt = Optimize()

# Decision variables:
# d: day of the meeting (0 to 4)
# s: start time in minutes after midnight
d = Int("d")
s = Int("s")

# The meeting must be scheduled within work hours.
opt.add(s >= WORK_START, s + duration <= WORK_END)
opt.add(d >= 0, d <= 4)

# Add Jeffrey's busy schedule constraints.
for day, intervals in jeffrey_busy.items():
    for (busy_start, busy_end) in intervals:
        # When the meeting is on a day, it should not overlap with any busy interval.
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Add Timothy's busy schedule constraints.
for day, intervals in timothy_busy.items():
    for (busy_start, busy_end) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Soft objective: schedule as early as possible by minimizing (day*WORK_END + start time)
earliest_expr = d * WORK_END + s
opt.minimize(earliest_expr)

# Solve and print the result.
if opt.check() == sat:
    model = opt.model()
    meeting_day = model[d].as_long()
    meeting_start = model[s].as_long()
    meeting_end = meeting_start + duration

    sh, sm = divmod(meeting_start, 60)
    eh, em = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
        day_names[meeting_day], sh, sm, eh, em))
else:
    print("No valid meeting time found.")