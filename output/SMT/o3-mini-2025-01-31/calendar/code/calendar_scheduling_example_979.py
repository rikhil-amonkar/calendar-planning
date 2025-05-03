from z3 import Optimize, Int, If, Or, sat

# Meeting parameters
duration = 30               # meeting duration in minutes (30 minutes)
WORK_START = 9 * 60         # 9:00 AM in minutes (540)
WORK_END = 17 * 60          # 17:00 in minutes (1020)

# Days of week: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Catherine's blocked intervals (times in minutes after midnight)
catherine_busy = {
    0: [  # Monday
        (9 * 60, 9 * 60 + 30),         # 9:00 to 9:30
        (10 * 60, 10 * 60 + 30),       # 10:00 to 10:30
        (11 * 60, 11 * 60 + 30),       # 11:00 to 11:30
        (12 * 60 + 30, 14 * 60),       # 12:30 to 14:00
        (14 * 60 + 30, 15 * 60),       # 14:30 to 15:00
        (15 * 60 + 30, 16 * 60 + 30)   # 15:30 to 16:30
    ],
    1: [  # Tuesday
        (10 * 60 + 30, 11 * 60),       # 10:30 to 11:00
        (12 * 60 + 30, 13 * 60),       # 12:30 to 13:00
        (15 * 60 + 30, 16 * 60),       # 15:30 to 16:00
        (16 * 60 + 30, 17 * 60)        # 16:30 to 17:00
    ],
    2: [  # Wednesday
        (9 * 60 + 30, 10 * 60),        # 9:30 to 10:00
        (10 * 60 + 30, 11 * 60),       # 10:30 to 11:00
        (13 * 60 + 30, 16 * 60)        # 13:30 to 16:00
    ],
    3: [  # Thursday
        (9 * 60, 11 * 60),             # 9:00 to 11:00
        (12 * 60 + 30, 15 * 60),       # 12:30 to 15:00
        (16 * 60, 17 * 60)             # 16:00 to 17:00
    ],
    4: [  # Friday
        (9 * 60, 10 * 60),             # 9:00 to 10:00
        (12 * 60, 12 * 60 + 30),       # 12:00 to 12:30
        (13 * 60, 13 * 60 + 30),       # 13:00 to 13:30
        (14 * 60, 14 * 60 + 30),       # 14:00 to 14:30
        (15 * 60 + 30, 16 * 60 + 30)   # 15:30 to 16:30
    ]
}

# Andrea's blocked intervals
andrea_busy = {
    0: [  # Monday
        (9 * 60 + 30, 10 * 60),        # 9:30 to 10:00
        (10 * 60 + 30, 11 * 60 + 30),    # 10:30 to 11:30
        (12 * 60, 13 * 60),            # 12:00 to 13:00
        (14 * 60, 15 * 60 + 30),       # 14:00 to 15:30
        (16 * 60 + 30, 17 * 60)        # 16:30 to 17:00
    ],
    1: [  # Tuesday
        (9 * 60 + 30, 10 * 60),        # 9:30 to 10:00
        (11 * 60 + 30, 13 * 60),       # 11:30 to 13:00
        (14 * 60, 14 * 60 + 30),       # 14:00 to 14:30
        (15 * 60, 15 * 60 + 30),       # 15:00 to 15:30
        (16 * 60, 17 * 60)            # 16:00 to 17:00
    ],
    2: [  # Wednesday
        (9 * 60 + 30, 10 * 60),        # 9:30 to 10:00
        (11 * 60, 11 * 60 + 30),       # 11:00 to 11:30
        (12 * 60, 13 * 60),            # 12:00 to 13:00
        (15 * 60, 16 * 60),            # 15:00 to 16:00
        (16 * 60 + 30, 17 * 60)        # 16:30 to 17:00
    ],
    3: [  # Thursday
        (9 * 60, 10 * 60 + 30),        # 9:00 to 10:30
        (11 * 60, 11 * 60 + 30),       # 11:00 to 11:30
        (13 * 60, 14 * 60 + 30),       # 13:00 to 14:30
        (15 * 60, 16 * 60 + 30)        # 15:00 to 16:30
    ],
    4: [  # Friday
        (9 * 60, 9 * 60 + 30),         # 9:00 to 9:30
        (10 * 60, 11 * 60),            # 10:00 to 11:00
        (12 * 60, 12 * 60 + 30),       # 12:00 to 12:30
        (13 * 60, 14 * 60),            # 13:00 to 14:00
        (14 * 60 + 30, 15 * 60),       # 14:30 to 15:00
        (16 * 60 + 30, 17 * 60)        # 16:30 to 17:00
    ]
}

# Helper function to check that the meeting does not overlap with a busy interval.
def no_overlap(meet_start, meet_duration, busy_start, busy_end):
    # Meeting must either finish before the busy interval starts,
    # or start after the busy interval ends.
    return Or(meet_start + meet_duration <= busy_start, meet_start >= busy_end)

# Create the Z3 Optimize solver.
opt = Optimize()

# Define decision variables:
# d: day of the meeting (0 to 4) and s: start time in minutes from midnight.
d = Int("d")
s = Int("s")

# The meeting must be scheduled within work hours.
opt.add(s >= WORK_START, s + duration <= WORK_END)
opt.add(d >= 0, d <= 4)

# Add busy constraints for Catherine.
for day, intervals in catherine_busy.items():
    for (busy_start, busy_end) in intervals:
        # Enforce the no overlap constraint if the meeting is on that day.
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Add busy constraints for Andrea.
for day, intervals in andrea_busy.items():
    for (busy_start, busy_end) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Soft objective: schedule at the earliest availability.
# "Earliest" is defined by the day and then the start time.
earliest_expr = d * WORK_END + s
opt.minimize(earliest_expr)

# Check for a solution and print the meeting time.
if opt.check() == sat:
    model = opt.model()
    meeting_day = model[d].as_long()
    meeting_start = model[s].as_long()
    meeting_end = meeting_start + duration

    start_hour, start_minute = divmod(meeting_start, 60)
    end_hour, end_minute = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
        day_names[meeting_day], start_hour, start_minute, end_hour, end_minute))
else:
    print("No valid meeting time found.")