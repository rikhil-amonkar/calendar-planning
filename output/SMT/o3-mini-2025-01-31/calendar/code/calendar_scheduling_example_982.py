from z3 import Optimize, Int, If, Or, sat

# Meeting parameters
duration = 30               # Duration in minutes (30 minutes)
WORK_START = 9 * 60         # 9:00 in minutes (540)
WORK_END = 17 * 60          # 17:00 in minutes (1020)

# Map days to numbers: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Emma's busy schedule (times in minutes after midnight)
emma_busy = {
    0: [  # Monday
        (9 * 60, 9 * 60 + 30),      # 9:00 to 9:30
        (15 * 60, 15 * 60 + 30)     # 15:00 to 15:30
    ],
    1: [  # Tuesday
        (11 * 60 + 30, 12 * 60),    # 11:30 to 12:00
        (12 * 60 + 30, 13 * 60)     # 12:30 to 13:00
    ],
    2: [  # Wednesday
        (9 * 60, 9 * 60 + 30),      # 9:00 to 9:30
        (11 * 60, 11 * 60 + 30),    # 11:00 to 11:30
        (13 * 60 + 30, 14 * 60 + 30),  # 13:30 to 14:30
        (16 * 60, 16 * 60 + 30)     # 16:00 to 16:30
    ],
    3: [  # Thursday
        (11 * 60, 11 * 60 + 30),    # 11:00 to 11:30
        (12 * 60, 12 * 60 + 30),    # 12:00 to 12:30
        (16 * 60 + 30, 17 * 60)     # 16:30 to 17:00
    ],
    4: [  # Friday
        (10 * 60 + 30, 11 * 60),    # 10:30 to 11:00
        (12 * 60, 12 * 60 + 30)     # 12:00 to 12:30
    ]
}

# Jason's busy schedule (times in minutes after midnight)
jason_busy = {
    0: [  # Monday
        (9 * 60, 17 * 60)          # 9:00 to 17:00 (completely busy)
    ],
    1: [  # Tuesday
        (9 * 60, 11 * 60 + 30),     # 9:00 to 11:30
        (12 * 60, 17 * 60)          # 12:00 to 17:00
    ],
    2: [  # Wednesday
        (10 * 60, 11 * 60 + 30),    # 10:00 to 11:30
        (12 * 60, 13 * 60),         # 12:00 to 13:00
        (13 * 60 + 30, 15 * 60 + 30),# 13:30 to 15:30
        (16 * 60, 17 * 60)          # 16:00 to 17:00
    ],
    3: [  # Thursday
        (9 * 60, 11 * 60 + 30),     # 9:00 to 11:30
        (12 * 60 + 30, 13 * 60),    # 12:30 to 13:00
        (13 * 60 + 30, 15 * 60),    # 13:30 to 15:00
        (15 * 60 + 30, 17 * 60)     # 15:30 to 17:00
    ],
    4: [  # Friday
        (9 * 60 + 30, 12 * 60 + 30),# 9:30 to 12:30
        (13 * 60 + 30, 16 * 60 + 30) # 13:30 to 16:30
    ]
}

# Helper function to ensure meeting does not overlap with a busy interval.
def no_overlap(meet_start, meet_duration, busy_start, busy_end):
    # Either the meeting finishes before the busy interval starts,
    # or starts after the busy interval ends.
    return Or(meet_start + meet_duration <= busy_start, meet_start >= busy_end)

# Create the Z3 optimizer
opt = Optimize()

# Decision variables:
# d : day of meeting (0-4)
# s : start time in minutes after midnight.
d = Int("d")
s = Int("s")

# Meeting must be within work hour limits.
opt.add(s >= WORK_START, s + duration <= WORK_END)
opt.add(d >= 0, d <= 4)

# Participant Preferences:
# Jason cannot meet on Wednesday; i.e., exclude day 2.
opt.add(d != 2)
# Jason cannot meet on Thursday after 14:00.
# If meeting is on Thursday (d==3), meeting must finish by 14:00 (i.e., s + duration <= 14*60)
opt.add(If(d == 3, s + duration <= 14 * 60, True))
# Jason cannot meet on Friday.
opt.add(d != 4)

# (Emma has no extra day preferences besides her busy schedule.)

# Add Emma's busy schedule constraints.
for day, intervals in emma_busy.items():
    for (busy_start, busy_end) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Add Jason's busy schedule constraints.
for day, intervals in jason_busy.items():
    for (busy_start, busy_end) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Soft objective: schedule the meeting as early as possible.
earliest_expr = d * WORK_END + s
opt.minimize(earliest_expr)

# Check for a solution and display the meeting time.
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