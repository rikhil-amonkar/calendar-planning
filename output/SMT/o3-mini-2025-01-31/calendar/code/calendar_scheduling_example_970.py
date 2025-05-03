from z3 import Optimize, Int, If, Or, And, sat

# Meeting parameters
duration = 60               # one hour meeting
WORK_START = 9 * 60         # 9:00 AM in minutes (540)
WORK_END = 17 * 60          # 17:00 in minutes (1020)

# Map numeric day to day names: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Hard busy times for Shirley
shirley_busy = {
    0: [  # Monday
        (13 * 60, 13 * 60 + 30)  # 13:00 to 13:30
    ],
    2: [  # Wednesday
        (14 * 60 + 30, 15 * 60)  # 14:30 to 15:00
    ],
    3: [  # Thursday
        (13 * 60, 13 * 60 + 30)  # 13:00 to 13:30
    ],
    4: [  # Friday
        (11 * 60 + 30, 12 * 60)  # 11:30 to 12:00
    ]
}

# Hard busy times for Sophia
sophia_busy = {
    0: [  # Monday
        (10 * 60, 12 * 60),       # 10:00 to 12:00
        (12 * 60 + 30, 13 * 60),  # 12:30 to 13:00
        (13 * 60 + 30, 14 * 60 + 30),  # 13:30 to 14:30
        (15 * 60, 16 * 60)        # 15:00 to 16:00
    ],
    1: [  # Tuesday
        (9 * 60, 9 * 60 + 30),    # 9:00 to 9:30
        (10 * 60 + 30, 12 * 60),  # 10:30 to 12:00
        (12 * 60 + 30, 13 * 60),  # 12:30 to 13:00
        (13 * 60 + 30, 14 * 60 + 30),  # 13:30 to 14:30
        (15 * 60 + 30, 17 * 60)   # 15:30 to 17:00
    ],
    2: [  # Wednesday
        (9 * 60, 10 * 60),        # 9:00 to 10:00
        (12 * 60, 12 * 60 + 30),  # 12:00 to 12:30
        (13 * 60, 13 * 60 + 30),  # 13:00 to 13:30
        (14 * 60 + 30, 15 * 60),  # 14:30 to 15:00
        (16 * 60, 17 * 60)        # 16:00 to 17:00
    ],
    3: [  # Thursday
        (9 * 60, 9 * 60 + 30),    # 9:00 to 9:30
        (10 * 60 + 30, 11 * 60 + 30),  # 10:30 to 11:30
        (12 * 60, 13 * 60),       # 12:00 to 13:00
        (15 * 60 + 30, 16 * 60),  # 15:30 to 16:00
        (16 * 60 + 30, 17 * 60)   # 16:30 to 17:00
    ],
    4: [  # Friday
        (9 * 60, 10 * 60),        # 9:00 to 10:00
        (10 * 60 + 30, 11 * 60),   # 10:30 to 11:00
        (11 * 60 + 30, 12 * 60),   # 11:30 to 12:00
        (13 * 60, 14 * 60 + 30),   # 13:00 to 14:30
        (15 * 60, 15 * 60 + 30),   # 15:00 to 15:30
        (16 * 60, 16 * 60 + 30)    # 16:00 to 16:30
    ]
}

# Helper: meeting interval [s, s+duration) must not overlap with a busy interval [bstart, bend)
def no_overlap(s, duration, bstart, bend):
    return Or(s + duration <= bstart, s >= bend)

# Create an optimizer instance
opt = Optimize()

# Variables:
# d: meeting day (0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday)
# s: meeting start time in minutes (from midnight)
d = Int("d")
s = Int("s")

# Basic constraints: meeting day is between 0 and 4 and meeting must occur within work hours.
opt.add(d >= 0, d <= 4)
opt.add(s >= WORK_START, s + duration <= WORK_END)

# HARD constraint: Shirley cannot meet on Friday.
opt.add(d != 4)

# Hard constraints for Shirley's busy times.
for day in shirley_busy:
    for (bstart, bend) in shirley_busy[day]:
        opt.add(If(d == day, no_overlap(s, duration, bstart, bend), True))

# Hard constraints for Sophia's busy times.
for day in sophia_busy:
    for (bstart, bend) in sophia_busy[day]:
        opt.add(If(d == day, no_overlap(s, duration, bstart, bend), True))

# Soft constraints (preferences) for Sophia:
# Sophia does not want to meet on:
#    Monday (d==0),
#    Tuesday (d==1),
#    Thursday (d==3),
# or on Wednesday after 13:00 (d==2 and s >= 13:00 i.e., 780).
def compute_penalty(d, s):
    penalty = 0
    penalty += If(d == 0, 1, 0)  # avoid Monday
    penalty += If(d == 1, 1, 0)  # avoid Tuesday
    penalty += If(d == 3, 1, 0)  # avoid Thursday
    penalty += If(And(d == 2, s >= 13 * 60), 1, 0)  # avoid Wednesday after 13:00
    return penalty

penalty = compute_penalty(d, s)
opt.minimize(penalty)

# Secondary objective: schedule as early as possible
earliest = d * (WORK_END) + s
opt.minimize(earliest)

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