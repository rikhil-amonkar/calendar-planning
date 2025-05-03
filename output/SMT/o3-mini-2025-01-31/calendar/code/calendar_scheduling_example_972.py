from z3 import Optimize, Int, If, Or, And, sat

# Meeting parameters
duration = 30               # half an hour meeting
WORK_START = 9 * 60         # 9:00 AM in minutes (540)
WORK_END = 17 * 60          # 17:00 in minutes (1020)

# Map numeric day to day names: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Kelly's busy times by day
kelly_busy = {
    0: [  # Monday
        (9 * 60, 10 * 60),         # 9:00 to 10:00
        (10 * 60 + 30, 14 * 60 + 30),  # 10:30 to 14:30
        (16 * 60, 17 * 60)          # 16:00 to 17:00
    ],
    1: [  # Tuesday
        (9 * 60, 10 * 60),         # 9:00 to 10:00
        (10 * 60 + 30, 11 * 60),    # 10:30 to 11:00
        (11 * 60 + 30, 12 * 60),    # 11:30 to 12:00
        (15 * 60, 15 * 60 + 30),    # 15:00 to 15:30
        (16 * 60 + 30, 17 * 60)     # 16:30 to 17:00
    ],
    2: [  # Wednesday
        (9 * 60, 9 * 60 + 30),      # 9:00 to 9:30
        (11 * 60, 11 * 60 + 30),    # 11:00 to 11:30
        (12 * 60, 12 * 60 + 30),    # 12:00 to 12:30
        (14 * 60, 14 * 60 + 30),    # 14:00 to 14:30
        (15 * 60, 16 * 60)          # 15:00 to 16:00
    ],
    3: [  # Thursday
        (11 * 60, 12 * 60 + 30),    # 11:00 to 12:30
        (13 * 60 + 30, 14 * 60),    # 13:30 to 14:00
        (15 * 60, 15 * 60 + 30),    # 15:00 to 15:30
        (16 * 60, 17 * 60)          # 16:00 to 17:00
    ],
    4: [  # Friday
        (11 * 60, 12 * 60),        # 11:00 to 12:00
        (13 * 60, 13 * 60 + 30),    # 13:00 to 13:30
        (14 * 60 + 30, 15 * 60 + 30)  # 14:30 to 15:30
    ]
}

# Michelle's busy times by day
michelle_busy = {
    0: [  # Monday
        (9 * 60, 10 * 60),         # 9:00 to 10:00
        (11 * 60, 13 * 60),        # 11:00 to 13:00
        (13 * 60 + 30, 15 * 60 + 30),  # 13:30 to 15:30
        (16 * 60, 16 * 60 + 30)     # 16:00 to 16:30
    ],
    1: [  # Tuesday
        (9 * 60, 9 * 60 + 30),      # 9:00 to 9:30
        (10 * 60, 10 * 60 + 30),    # 10:00 to 10:30
        (11 * 60, 17 * 60)          # 11:00 to 17:00
    ],
    2: [  # Wednesday
        (9 * 60, 17 * 60)          # 9:00 to 17:00 (completely busy)
    ],
    3: [  # Thursday
        (9 * 60, 17 * 60)          # 9:00 to 17:00 (completely busy)
    ],
    4: [  # Friday
        (9 * 60, 16 * 60 + 30)      # 9:00 to 16:30
    ]
}

# Helper function: a meeting starting at time 's' (lasting 'duration') does not overlap a busy interval (bstart, bend)
def no_overlap(s, duration, bstart, bend):
    # either the meeting finishes on or before busy starts, or starts on or after busy ends
    return Or(s + duration <= bstart, s >= bend)

# Create an optimizer instance
opt = Optimize()

# Define variables:
# d: day of the meeting (0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday)
# s: meeting start time in minutes from midnight
d = Int("d")
s = Int("s")

# Basic constraints: valid day and meeting must lie inside work hours.
opt.add(d >= 0, d <= 4)
opt.add(s >= WORK_START, s + duration <= WORK_END)

# Add hard constraints to avoid overlapping busy times for Kelly
for day, intervals in kelly_busy.items():
    for (bstart, bend) in intervals:
        # if meeting is on this day, then it must not overlap with the busy interval.
        opt.add(If(d == day, no_overlap(s, duration, bstart, bend), True))

# Add hard constraints to avoid overlapping busy times for Michelle
for day, intervals in michelle_busy.items():
    for (bstart, bend) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, bstart, bend), True))

# Soft objective: meet as early as possible.
# We define "earliest" by minimizing day * WORK_END + s.
earliest_expr = d * (WORK_END) + s
opt.minimize(earliest_expr)

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
    print("No valid meeting time found that satisfies all constraints.")