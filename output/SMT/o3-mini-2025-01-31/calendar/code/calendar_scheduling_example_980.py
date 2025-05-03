from z3 import Optimize, Int, If, Or, sat

# Meeting parameters
duration = 30               # meeting duration in minutes (30 minutes)
WORK_START = 9 * 60         # 9:00 AM in minutes (540)
WORK_END = 17 * 60          # 17:00 in minutes (1020)

# Days of week: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Megan's blocked intervals (times in minutes after midnight)
megan_busy = {
    0: [  # Monday
        (15 * 60, 15 * 60 + 30)       # 15:00 to 15:30 (900,930)
    ],
    1: [  # Tuesday
        (9 * 60 + 30, 10 * 60),        # 9:30 to 10:00 (570,600)
        (11 * 60 + 30, 12 * 60),       # 11:30 to 12:00 (690,720)
        (15 * 60 + 30, 16 * 60)        # 15:30 to 16:00 (930,960)
    ],
    2: [  # Wednesday
        (9 * 60, 10 * 60),            # 9:00 to 10:00 (540,600)
        (10 * 60 + 30, 11 * 60),       # 10:30 to 11:00 (630,660)
        (11 * 60 + 30, 13 * 60),       # 11:30 to 13:00 (690,780)
        (13 * 60 + 30, 14 * 60),       # 13:30 to 14:00 (810,840)
        (14 * 60 + 30, 15 * 60),       # 14:30 to 15:00 (870,900)
        (15 * 60 + 30, 16 * 60 + 30)   # 15:30 to 16:30 (930,990)
    ],
    3: [  # Thursday
        (11 * 60, 11 * 60 + 30),       # 11:00 to 11:30 (660,690)
        (12 * 60, 13 * 60),           # 12:00 to 13:00 (720,780)
        (14 * 60, 16 * 60),           # 14:00 to 16:00 (840,960)
        (16 * 60 + 30, 17 * 60)       # 16:30 to 17:00 (990,1020)
    ],
    4: [  # Friday
        (10 * 60, 10 * 60 + 30),       # 10:00 to 10:30 (600,630)
        (13 * 60, 13 * 60 + 30),       # 13:00 to 13:30 (780,810)
        (15 * 60, 15 * 60 + 30),       # 15:00 to 15:30 (900,930)
        (16 * 60 + 30, 17 * 60)        # 16:30 to 17:00 (990,1020)
    ]
}

# Joan's blocked intervals (times in minutes after midnight)
joan_busy = {
    0: [  # Monday
        (9 * 60, 9 * 60 + 30),         # 9:00 to 9:30 (540,570)
        (10 * 60, 10 * 60 + 30),       # 10:00 to 10:30 (600,630)
        (11 * 60, 13 * 60 + 30),       # 11:00 to 13:30 (660,810)
        (15 * 60, 16 * 60 + 30)        # 15:00 to 16:30 (900,990)
    ],
    1: [  # Tuesday
        (9 * 60, 9 * 60 + 30),         # 9:00 to 9:30 (540,570)
        (10 * 60, 10 * 60 + 30),       # 10:00 to 10:30 (600,630)
        (11 * 60, 11 * 60 + 30),       # 11:00 to 11:30 (660,690)
        (12 * 60 + 30, 13 * 60),       # 12:30 to 13:00 (750,780)
        (14 * 60, 17 * 60)            # 14:00 to 17:00 (840,1020)
    ],
    2: [  # Wednesday
        (9 * 60 + 30, 12 * 60),        # 9:30 to 12:00 (570,720)
        (12 * 60 + 30, 14 * 60),       # 12:30 to 14:00 (750,840)
        (14 * 60 + 30, 16 * 60),       # 14:30 to 16:00 (870,960)
        (16 * 60 + 30, 17 * 60)        # 16:30 to 17:00 (990,1020)
    ],
    3: [  # Thursday
        (9 * 60 + 30, 11 * 60),        # 9:30 to 11:00 (570,660)
        (12 * 60, 12 * 60 + 30),       # 12:00 to 12:30 (720,750)
        (13 * 60, 15 * 60),           # 13:00 to 15:00 (780,900)
        (15 * 60 + 30, 17 * 60)        # 15:30 to 17:00 (930,1020)
    ],
    4: [  # Friday
        (9 * 60 + 30, 10 * 60),         # 9:30 to 10:00 (570,600)
        (12 * 60, 13 * 60)            # 12:00 to 13:00 (720,780)
    ]
}

# Helper function: meeting does not overlap with a busy interval.
def no_overlap(meet_start, meet_duration, busy_start, busy_end):
    # A meeting and a busy interval don't overlap if the meeting ends
    # before the busy interval starts or begins after the busy interval ends.
    return Or(meet_start + meet_duration <= busy_start, meet_start >= busy_end)

# Create the Z3 Optimize solver.
opt = Optimize()

# Decision variables:
# d: the day of the meeting (0 to 4)
# s: the meeting start time in minutes from midnight.
d = Int("d")
s = Int("s")

# The meeting must be scheduled within work hours.
opt.add(s >= WORK_START, s + duration <= WORK_END)
opt.add(d >= 0, d <= 4)

# Add Megan's additional preferences:
# Megan wants to avoid meetings on Tuesday (d == 1) and Friday (d == 4).
# And she wants to avoid meetings on Thursday after 9:30 (i.e. meeting must end by 9:30 on Thursday).
opt.add(d != 1)   # avoid Tuesday
opt.add(d != 4)   # avoid Friday
opt.add(If(d == 3, s + duration <= 9 * 60 + 30, True))  # if Thursday, meeting must end no later than 9:30

# Add Joan's additional restrictions:
# Joan can not meet on Monday (d == 0) or Wednesday (d == 2).
opt.add(d != 0)
opt.add(d != 2)

# With the above participant preferences, the only possible day is Thursday (d == 3).
# However, we still add their busy schedule constraints.
     
# Add Megan's busy schedule constraints.
for day, intervals in megan_busy.items():
    for (busy_start, busy_end) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))
        
# Add Joan's busy schedule constraints.
for day, intervals in joan_busy.items():
    for (busy_start, busy_end) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Soft objective: schedule the meeting at the earliest availability.
# Earlier availability is measured by the value of d * WORK_END + s.
earliest_expr = d * WORK_END + s
opt.minimize(earliest_expr)

# Check for a solution and output the meeting time.
if opt.check() == sat:
    model = opt.model()
    meeting_day = model[d].as_long()
    meeting_start = model[s].as_long()
    meeting_end = meeting_start + duration

    start_hour, start_minute = divmod(meeting_start, 60)
    end_hour, end_minute = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
        day_names[meeting_day], start_hour, start_minute, end_hour, end_minute)
    )
else:
    print("No valid meeting time found.")