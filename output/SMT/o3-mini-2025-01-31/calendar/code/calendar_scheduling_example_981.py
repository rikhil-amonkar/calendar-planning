from z3 import Optimize, Int, If, Or, sat

# Meeting parameters
duration = 30               # meeting duration in minutes (30 minutes)
WORK_START = 9 * 60         # 9:00 AM in minutes (540)
WORK_END = 17 * 60          # 17:00 in minutes (1020)

# Days of week mapping: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Virginia's busy schedule (times in minutes after midnight)
virginia_busy = {
    0: [  # Monday
        (9 * 60 + 30, 10 * 60)       # 9:30 to 10:00
    ],
    1: [  # Tuesday
        (14 * 60, 14 * 60 + 30),      # 14:00 to 14:30
        (16 * 60 + 30, 17 * 60)       # 16:30 to 17:00
    ],
    2: [  # Wednesday
        (13 * 60 + 30, 14 * 60)       # 13:30 to 14:00
    ],
    3: [  # Thursday
        (12 * 60 + 30, 13 * 60 + 30)   # 12:30 to 13:30
    ],
    4: []  # Friday: no meetings scheduled for Virginia
}

# Joyce's busy schedule (times in minutes after midnight)
joyce_busy = {
    0: [  # Monday
        (9 * 60 + 30, 13 * 60 + 30),  # 9:30 to 13:30
        (14 * 60, 14 * 60 + 30),      # 14:00 to 14:30
        (15 * 60, 17 * 60)            # 15:00 to 17:00
    ],
    1: [  # Tuesday
        (9 * 60, 10 * 60),           # 9:00 to 10:00
        (10 * 60 + 30, 11 * 60 + 30),  # 10:30 to 11:30
        (12 * 60, 13 * 60),          # 12:00 to 13:00
        (14 * 60, 17 * 60)           # 14:00 to 17:00
    ],
    2: [  # Wednesday
        (9 * 60, 10 * 60 + 30),       # 9:00 to 10:30
        (11 * 60, 11 * 60 + 30),      # 11:00 to 11:30
        (12 * 60, 15 * 60),           # 12:00 to 15:00
        (16 * 60, 17 * 60)            # 16:00 to 17:00
    ],
    3: [  # Thursday
        (9 * 60, 17 * 60)            # 9:00 to 17:00 (all day busy)
    ],
    4: [  # Friday
        (9 * 60, 9 * 60 + 30),       # 9:00 to 9:30
        (10 * 60, 12 * 60),          # 10:00 to 12:00
        (12 * 60 + 30, 16 * 60 + 30)  # 12:30 to 16:30
    ]
}

# Helper function: meeting does not overlap with a busy interval.
def no_overlap(meet_start, meet_duration, busy_start, busy_end):
    # The meeting must finish before the busy interval begins,
    # or start after the busy interval ends.
    return Or(meet_start + meet_duration <= busy_start, meet_start >= busy_end)

# Create the Z3 Optimize solver.
opt = Optimize()

# Decision variables:
# d: day of the meeting (0 to 4)
# s: start time in minutes from midnight.
d = Int("d")
s = Int("s")

# Ensure the meeting is within working hours.
opt.add(s >= WORK_START, s + duration <= WORK_END)
opt.add(d >= 0, d <= 4)

# Participant preferences:
# Virginia would rather not meet on Tuesday -> avoid day 1.
opt.add(d != 1)
# Virginia would rather not have meetings on Wednesday after 12:30.
# So if meeting is on Wednesday (day 2), it must finish by 12:30 (i.e. s + duration <= 12:30 which is 750 minutes).
opt.add(If(d == 2, s + duration <= 12 * 60 + 30, True))

# Joyce would like to avoid more meetings on Monday and Friday -> avoid days 0 and 4.
opt.add(d != 0, d != 4)

# Add Virginia's busy time constraints.
for day, intervals in virginia_busy.items():
    for (busy_start, busy_end) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Add Joyce's busy time constraints.
for day, intervals in joyce_busy.items():
    for (busy_start, busy_end) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Soft objective: schedule at the earliest availability by minimizing (d * WORK_END + s)
earliest_expr = d * WORK_END + s
opt.minimize(earliest_expr)

# Check for a solution and print out the meeting time.
if opt.check() == sat:
    model = opt.model()
    meeting_day = model[d].as_long()
    meeting_start = model[s].as_long()
    meeting_end = meeting_start + duration

    start_hour, start_minute = divmod(meeting_start, 60)
    end_hour, end_minute = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
        day_names[meeting_day], start_hour, start_minute, end_hour, end_minute
    ))
else:
    print("No valid meeting time found.")