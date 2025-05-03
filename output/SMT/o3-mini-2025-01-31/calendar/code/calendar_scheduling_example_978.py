from z3 import Optimize, Int, If, Or, sat

# Meeting parameters
duration = 60               # 60 minutes (1 hour)
WORK_START = 9 * 60         # 9:00 AM in minutes (540)
WORK_END = 17 * 60          # 17:00 in minutes (1020)

# Days of week: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Brian's busy intervals (times in minutes after midnight)
brian_busy = {
    0: [  # Monday
        (9 * 60 + 30, 10 * 60),       # 9:30 to 10:00
        (12 * 60 + 30, 14 * 60 + 30),  # 12:30 to 14:30
        (15 * 60 + 30, 16 * 60)        # 15:30 to 16:00
    ],
    1: [  # Tuesday
        (9 * 60, 9 * 60 + 30)          # 9:00 to 9:30
    ],
    2: [  # Wednesday
        (12 * 60 + 30, 14 * 60),       # 12:30 to 14:00
        (16 * 60 + 30, 17 * 60)        # 16:30 to 17:00
    ],
    3: [  # Thursday
        (11 * 60, 11 * 60 + 30),       # 11:00 to 11:30
        (13 * 60, 13 * 60 + 30),       # 13:00 to 13:30
        (16 * 60 + 30, 17 * 60)        # 16:30 to 17:00
    ],
    4: [  # Friday
        (9 * 60 + 30, 10 * 60),        # 9:30 to 10:00
        (10 * 60 + 30, 11 * 60),       # 10:30 to 11:00
        (13 * 60, 13 * 60 + 30),       # 13:00 to 13:30
        (15 * 60, 16 * 60),            # 15:00 to 16:00
        (16 * 60 + 30, 17 * 60)        # 16:30 to 17:00
    ]
}

# Julia's busy intervals (times in minutes after midnight)
julia_busy = {
    0: [  # Monday
        (9 * 60, 10 * 60),            # 9:00 to 10:00
        (11 * 60, 11 * 60 + 30),      # 11:00 to 11:30
        (12 * 60 + 30, 13 * 60),      # 12:30 to 13:00
        (15 * 60 + 30, 16 * 60)       # 15:30 to 16:00
    ],
    1: [  # Tuesday
        (13 * 60, 14 * 60),          # 13:00 to 14:00
        (16 * 60, 16 * 60 + 30)      # 16:00 to 16:30
    ],
    2: [  # Wednesday
        (9 * 60, 11 * 60 + 30),       # 9:00 to 11:30
        (12 * 60, 12 * 60 + 30),      # 12:00 to 12:30
        (13 * 60, 17 * 60)           # 13:00 to 17:00
    ],
    3: [  # Thursday
        (9 * 60, 10 * 60 + 30),       # 9:00 to 10:30
        (11 * 60, 17 * 60)           # 11:00 to 17:00
    ],
    4: [  # Friday
        (9 * 60, 10 * 60),            # 9:00 to 10:00
        (10 * 60 + 30, 11 * 60 + 30),  # 10:30 to 11:30
        (12 * 60 + 30, 14 * 60),       # 12:30 to 14:00
        (14 * 60 + 30, 15 * 60),       # 14:30 to 15:00
        (15 * 60 + 30, 16 * 60)        # 15:30 to 16:00
    ]
}

# Helper function ensuring meeting does not overlap with a busy interval.
def no_overlap(meet_start, meet_duration, busy_start, busy_end):
    # Meeting must finish before busy period starts or start after it ends.
    return Or(meet_start + meet_duration <= busy_start, meet_start >= busy_end)

# Create the Z3 Optimize solver.
opt = Optimize()

# Decision variables:
# d: meeting day (0 to 4)
# s: meeting start time (in minutes from midnight)
d = Int("d")
s = Int("s")

# Meeting must occur within working hours on a valid day.
opt.add(s >= WORK_START, s + duration <= WORK_END)
opt.add(d >= 0, d <= 4)

# Participant preferences:
# Brian would like to avoid Monday. We'll add that as a hard constraint.
opt.add(d != 0)

# Add busy constraints for Brian.
for day, intervals in brian_busy.items():
    for (bstart, bend) in intervals:
        # Only enforce constraint on the corresponding day.
        opt.add(If(d == day, no_overlap(s, duration, bstart, bend), True))

# Add busy constraints for Julia.
for day, intervals in julia_busy.items():
    for (bstart, bend) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, bstart, bend), True))

# Soft objective: schedule at the earliest availability.
# We determine "earliest" as a combination of day and start time.
earliest_expr = d * WORK_END + s  # Lower value => earlier meeting
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