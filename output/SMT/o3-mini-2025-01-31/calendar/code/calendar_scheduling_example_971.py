from z3 import Optimize, Int, If, Or, And, sat

# Meeting parameters
duration = 30               # half an hour meeting
WORK_START = 9 * 60         # 9:00 AM in minutes (540)
WORK_END = 17 * 60          # 17:00 in minutes (1020)

# Map numeric day to day names: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Timothy's busy times (hard constraints) by day
timothy_busy = {
    0: [  # Monday
        (9 * 60, 9 * 60 + 30),      # 9:00 to 9:30
        (12 * 60, 12 * 60 + 30),    # 12:00 to 12:30
        (13 * 60, 14 * 60)          # 13:00 to 14:00
    ],
    1: [  # Tuesday
        (9 * 60, 9 * 60 + 30),      # 9:00 to 9:30
        (13 * 60, 13 * 60 + 30)     # 13:00 to 13:30
    ],
    2: [  # Wednesday
        (9 * 60, 9 * 60 + 30),      # 9:00 to 9:30
        (11 * 60, 12 * 60),         # 11:00 to 12:00
        (12 * 60 + 30, 14 * 60),    # 12:30 to 14:00
        (16 * 60, 16 * 60 + 30)     # 16:00 to 16:30
    ],
    3: [  # Thursday
        (9 * 60 + 30, 10 * 60),     # 9:30 to 10:00
        (10 * 60 + 30, 12 * 60),    # 10:30 to 12:00
        (12 * 60 + 30, 14 * 60),    # 12:30 to 14:00
        (14 * 60 + 30, 16 * 60 + 30)  # 14:30 to 16:30
    ],
    4: [  # Friday
        (10 * 60 + 30, 11 * 60),    # 10:30 to 11:00
        (12 * 60 + 30, 13 * 60),    # 12:30 to 13:00
        (13 * 60 + 30, 14 * 60 + 30),# 13:30 to 14:30
        (15 * 60, 16 * 60)          # 15:00 to 16:00
    ]
}

# Dennis's busy times (hard constraints) by day
dennis_busy = {
    0: [  # Monday
        (9 * 60 + 30, 11 * 60 + 30),  # 9:30 to 11:30
        (12 * 60, 13 * 60 + 30),      # 12:00 to 13:30
        (15 * 60, 15 * 60 + 30),      # 15:00 to 15:30
        (16 * 60, 17 * 60)            # 16:00 to 17:00
    ],
    1: [  # Tuesday
        (9 * 60, 9 * 60 + 30),        # 9:00 to 9:30
        (10 * 60 + 30, 11 * 60),       # 10:30 to 11:00
        (12 * 60 + 30, 13 * 60 + 30),  # 12:30 to 13:30
        (14 * 60, 15 * 60),           # 14:00 to 15:00
        (15 * 60 + 30, 16 * 60),      # 15:30 to 16:00
        (16 * 60 + 30, 17 * 60)       # 16:30 to 17:00
    ],
    2: [  # Wednesday
        (10 * 60, 10 * 60 + 30),      # 10:00 to 10:30
        (11 * 60 + 30, 12 * 60 + 30),  # 11:30 to 12:30
        (13 * 60, 14 * 60),           # 13:00 to 14:00
        (16 * 60 + 30, 17 * 60)       # 16:30 to 17:00
    ],
    3: [  # Thursday
        (9 * 60 + 30, 10 * 60),       # 9:30 to 10:00
        (11 * 60, 15 * 60),           # 11:00 to 15:00
        (15 * 60 + 30, 17 * 60)       # 15:30 to 17:00
    ],
    4: [  # Friday
        (10 * 60, 11 * 60),          # 10:00 to 11:00
        (12 * 60, 12 * 60 + 30),      # 12:00 to 12:30
        (14 * 60, 15 * 60),           # 14:00 to 15:00
        (15 * 60 + 30, 16 * 60)       # 15:30 to 16:00
    ]
}

# Helper function: meeting interval [s, s+duration) must not overlap with a busy interval [bstart, bend)
def no_overlap(s, duration, bstart, bend):
    return Or(s + duration <= bstart, s >= bend)

# Create an optimizer instance
opt = Optimize()

# Variables:
# d: meeting day (0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday)
# s: meeting start time in minutes (since midnight)
d = Int("d")
s = Int("s")

# Basic constraints: valid day and meeting time fits in working hours
opt.add(d >= 0, d <= 4)
opt.add(s >= WORK_START, s + duration <= WORK_END)

# Hard constraints for Timothy's busy times
for day in timothy_busy:
    for (bstart, bend) in timothy_busy[day]:
        # If the meeting is scheduled on this day, ensure it does not overlap with busy interval.
        opt.add(If(d == day, no_overlap(s, duration, bstart, bend), True))

# Hard constraints for Dennis's busy times
for day in dennis_busy:
    for (bstart, bend) in dennis_busy[day]:
        opt.add(If(d == day, no_overlap(s, duration, bstart, bend), True))

# Soft preferences:
# Timothy would like to avoid Monday (day 0)
# Dennis would like to avoid Friday (day 4)
def compute_penalty(d):
    penalty = 0
    penalty += If(d == 0, 1, 0)  # penalty for meeting on Monday (Timothy)
    penalty += If(d == 4, 1, 0)  # penalty for meeting on Friday (Dennis)
    return penalty

penalty = compute_penalty(d)
opt.minimize(penalty)

# Secondary objective: schedule at the earliest availability.
# We define "earliest" as minimizing d*(WORK_END) + s.
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