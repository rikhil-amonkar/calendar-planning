from z3 import Optimize, Int, If, Or, sat

# Meeting parameters
duration = 60               # one hour meeting
WORK_START = 9 * 60         # 9:00 in minutes (540)
WORK_END = 17 * 60          # 17:00 in minutes (1020)

# Map days: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Nicole's busy times by day (in minutes from midnight)
nicole_busy = {
    1: [  # Tuesday
        (16 * 60, 16 * 60 + 30)  # 16:00-16:30
    ],
    2: [  # Wednesday
        (15 * 60, 15 * 60 + 30)  # 15:00-15:30
    ],
    4: [  # Friday
        (12 * 60, 12 * 60 + 30), # 12:00-12:30
        (15 * 60 + 30, 16 * 60)  # 15:30-16:00
    ]
    # Monday (0) and Thursday (3) Nicole is free.
}

# Daniel's busy times by day (in minutes)
daniel_busy = {
    0: [  # Monday
        (9 * 60, 12 * 60 + 30),   # 9:00-12:30
        (13 * 60, 13 * 60 + 30),   # 13:00-13:30
        (14 * 60, 16 * 60 + 30)    # 14:00-16:30
    ],
    1: [  # Tuesday
        (9 * 60, 10 * 60 + 30),    # 9:00-10:30
        (11 * 60 + 30, 12 * 60 + 30), # 11:30-12:30
        (13 * 60, 13 * 60 + 30),    # 13:00-13:30
        (15 * 60, 16 * 60),        # 15:00-16:00
        (16 * 60 + 30, 17 * 60)    # 16:30-17:00
    ],
    2: [  # Wednesday
        (9 * 60, 10 * 60),         # 9:00-10:00
        (11 * 60, 12 * 60 + 30),    # 11:00-12:30
        (13 * 60, 13 * 60 + 30),    # 13:00-13:30
        (14 * 60, 14 * 60 + 30),    # 14:00-14:30
        (16 * 60 + 30, 17 * 60)     # 16:30-17:00
    ],
    3: [  # Thursday
        (11 * 60, 12 * 60),        # 11:00-12:00
        (13 * 60, 14 * 60),        # 13:00-14:00
        (15 * 60, 15 * 60 + 30)     # 15:00-15:30
    ],
    4: [  # Friday
        (10 * 60, 11 * 60),        # 10:00-11:00
        (11 * 60 + 30, 12 * 60),    # 11:30-12:00
        (12 * 60 + 30, 14 * 60 + 30),# 12:30-14:30
        (15 * 60, 15 * 60 + 30),    # 15:00-15:30
        (16 * 60, 16 * 60 + 30)     # 16:00-16:30
    ]
}

# Helper: returns a constraint that the meeting [s, s+duration) does not overlap a busy interval [bstart, bend)
def no_overlap(s, duration, bstart, bend):
    return Or(s + duration <= bstart, s >= bend)

# Create an Optimize solver instance
opt = Optimize()

# Decision variables: 
# d represents the day (0: Monday, ... 4: Friday)
# s represents the meeting start time in minutes after midnight.
d = Int("d")
s = Int("s")

# Enforce working hours constraint
opt.add(s >= WORK_START, s + duration <= WORK_END)
opt.add(d >= 0, d <= 4)

# Add busy constraints for Nicole:
for day, busy_intervals in nicole_busy.items():
    for (bstart, bend) in busy_intervals:
        # Only enforce when meeting is on that day.
        opt.add(If(d == day, no_overlap(s, duration, bstart, bend), True))

# Add busy constraints for Daniel:
for day, busy_intervals in daniel_busy.items():
    for (bstart, bend) in busy_intervals:
        opt.add(If(d == day, no_overlap(s, duration, bstart, bend), True))

# Soft objective: schedule at the earliest combined day and start time.
# We weight the day by WORK_END and then add start time.
earliest_expr = d * WORK_END + s
opt.minimize(earliest_expr)

# Check for a solution and print the meeting time if found.
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