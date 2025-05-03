from z3 import Optimize, Int, If, Or, sat

# Meeting parameters
duration = 60               # meeting length in minutes (1 hour)
WORK_START = 9 * 60         # 9:00 AM expressed in minutes (540)
WORK_END   = 17 * 60        # 17:00 expressed in minutes (1020)

# Days of week: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Beverly's busy intervals (each tuple is (start, end) in minutes after midnight)
beverly_busy = {
    0: [  # Monday
        (11 * 60 + 30, 12 * 60 + 30),  # 11:30 to 12:30
        (14 * 60, 14 * 60 + 30)         # 14:00 to 14:30
    ],
    1: [  # Tuesday
        (9 * 60, 9 * 60 + 30),         # 9:00 to 9:30
        (11 * 60 + 30, 12 * 60 + 30),    # 11:30 to 12:30
        (13 * 60, 14 * 60),            # 13:00 to 14:00
        (14 * 60 + 30, 15 * 60),       # 14:30 to 15:00
        (16 * 60, 16 * 60 + 30)        # 16:00 to 16:30
    ],
    2: [  # Wednesday
        (11 * 60 + 30, 12 * 60 + 30),   # 11:30 to 12:30
        (15 * 60 + 30, 17 * 60)         # 15:30 to 17:00
    ],
    3: [  # Thursday
        (9 * 60, 11 * 60 + 30),         # 9:00 to 11:30
        (12 * 60, 12 * 60 + 30),        # 12:00 to 12:30
        (14 * 60, 16 * 60),             # 14:00 to 16:00
        (16 * 60 + 30, 17 * 60)         # 16:30 to 17:00
    ],
    4: [  # Friday
        (9 * 60, 10 * 60),             # 9:00 to 10:00
        (11 * 60, 11 * 60 + 30),       # 11:00 to 11:30
        (16 * 60, 16 * 60 + 30)        # 16:00 to 16:30
    ]
}

# Jordan's busy intervals (all times in minutes after midnight)
jordan_busy = {
    0: [  # Monday
        (10 * 60, 10 * 60 + 30),       # 10:00 to 10:30
        (11 * 60, 11 * 60 + 30),       # 11:00 to 11:30
        (12 * 60, 12 * 60 + 30),       # 12:00 to 12:30
        (13 * 60, 14 * 60),            # 13:00 to 14:00
        (14 * 60 + 30, 15 * 60),       # 14:30 to 15:00
        (16 * 60 + 30, 17 * 60)        # 16:30 to 17:00
    ],
    1: [  # Tuesday
        (9 * 60, 9 * 60 + 30),         # 9:00 to 9:30
        (10 * 60, 15 * 60),            # 10:00 to 15:00
        (15 * 60 + 30, 17 * 60)        # 15:30 to 17:00
    ],
    2: [  # Wednesday
        (10 * 60, 11 * 60),            # 10:00 to 11:00
        (11 * 60 + 30, 12 * 60),       # 11:30 to 12:00
        (13 * 60 + 30, 14 * 60 + 30)    # 13:30 to 14:30
    ],
    3: [  # Thursday
        (9 * 60, 10 * 60),             # 9:00 to 10:00
        (10 * 60 + 30, 11 * 60),        # 10:30 to 11:00
        (12 * 60, 13 * 60),            # 12:00 to 13:00
        (13 * 60 + 30, 14 * 60),        # 13:30 to 14:00
        (14 * 60 + 30, 16 * 60 + 30)    # 14:30 to 16:30
    ],
    4: [  # Friday
        (9 * 60, 10 * 60 + 30),        # 9:00 to 10:30
        (11 * 60 + 30, 14 * 60),       # 11:30 to 14:00
        (14 * 60 + 30, 15 * 60),       # 14:30 to 15:00
        (16 * 60 + 30, 17 * 60)        # 16:30 to 17:00
    ]
}

# Define a helper function to ensure that a meeting slot does not overlap with a busy interval.
def no_overlap(meeting_start, meeting_duration, busy_start, busy_end):
    # Either the meeting ends before the busy period starts,
    # or the meeting starts after the busy period ends.
    return Or(meeting_start + meeting_duration <= busy_start, meeting_start >= busy_end)

# Create the Z3 Optimize solver, enabling us to add an objective.
opt = Optimize()

# Decision variables:
# d: the day of the meeting (0 to 4)
# s: the meeting start time in minutes (from midnight)
d = Int("d")
s = Int("s")

# Meeting must be scheduled within working hours.
opt.add(s >= WORK_START, s + duration <= WORK_END)
opt.add(d >= 0, d <= 4)

# Participant-specific preferences and constraints:

# Jordan would rather not meet on Monday or Friday.
opt.add(d != 0, d != 4)

# Beverly would rather not meet on Wednesday after 11:30.
# Here we enforce that if the meeting is on Wednesday (day 2),
# then the meeting must finish by 11:30. That is, the start time s must be at most 11:30 - duration.
BEVERLY_WEDNESDAY_CUTOFF = 11 * 60 + 30  # 11:30
opt.add(If(d == 2, s + duration <= BEVERLY_WEDNESDAY_CUTOFF, True))

# Add Beverly's busy constraints.
for day, intervals in beverly_busy.items():
    for (bstart, bend) in intervals:
        # Only enforce busy constraint when meeting is scheduled on the corresponding day.
        opt.add(If(d == day, no_overlap(s, duration, bstart, bend), True))

# Add Jordan's busy constraints.
for day, intervals in jordan_busy.items():
    for (bstart, bend) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, bstart, bend), True))

# Soft objective: choose the earliest possible meeting time.
# We define "earliest" in terms of day and start time.
earliest_expr = d * WORK_END + s
opt.minimize(earliest_expr)

# Check the model and print the solution.
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