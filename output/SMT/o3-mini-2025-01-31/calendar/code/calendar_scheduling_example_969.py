from z3 import Optimize, Int, If, Or, And, sat

# Meeting parameters
duration = 30               # half an hour meeting
WORK_START = 9 * 60         # 9:00 AM in minutes (540)
WORK_END = 17 * 60          # 17:00 in minutes (1020)

# Map numeric day to day names: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Kelly's blocked times (hard constraints)
kelly_busy = {
    0: [  # Monday
        (11 * 60, 11 * 60 + 30),     # 11:00 to 11:30
        (13 * 60 + 30, 14 * 60 + 30),  # 13:30 to 14:30
        (15 * 60, 15 * 60 + 30),      # 15:00 to 15:30
        (16 * 60, 16 * 60 + 30)       # 16:00 to 16:30
    ],
    1: [  # Tuesday
        (9 * 60 + 30, 10 * 60),      # 9:30 to 10:00
        (11 * 60, 11 * 60 + 30),     # 11:00 to 11:30
        (13 * 60, 15 * 60 + 30)      # 13:00 to 15:30
    ],
    2: [  # Wednesday
        (10 * 60 + 30, 11 * 60),     # 10:30 to 11:00
        (12 * 60, 12 * 60 + 30),     # 12:00 to 12:30
        (13 * 60, 13 * 60 + 30),     # 13:00 to 13:30
        (15 * 60, 15 * 60 + 30)      # 15:00 to 15:30
    ],
    3: [  # Thursday
        (9 * 60, 9 * 60 + 30),       # 9:00 to 9:30
        (12 * 60, 12 * 60 + 30),     # 12:00 to 12:30
        (13 * 60 + 30, 14 * 60 + 30)  # 13:30 to 14:30
    ],
    4: [  # Friday
        (9 * 60 + 30, 10 * 60),      # 9:30 to 10:00
        (12 * 60 + 30, 13 * 60 + 30), # 12:30 to 13:30
        (14 * 60 + 30, 15 * 60 + 30), # 14:30 to 15:30
        (16 * 60 + 30, 17 * 60)       # 16:30 to 17:00
    ]
}

# Bobby's blocked times (hard constraints)
bobby_busy = {
    0: [  # Monday
        (9 * 60, 17 * 60)          # 9:00 to 17:00 (fully booked)
    ],
    1: [  # Tuesday
        (9 * 60, 17 * 60)          # 9:00 to 17:00 (fully booked)
    ],
    2: [  # Wednesday
        (9 * 60, 11 * 60 + 30),     # 9:00 to 11:30
        (12 * 60, 16 * 60 + 30)     # 12:00 to 16:30
    ],
    3: [  # Thursday
        (9 * 60, 14 * 60 + 30),     # 9:00 to 14:30
        (15 * 60, 17 * 60)          # 15:00 to 17:00
    ],
    4: [  # Friday
        (9 * 60 + 30, 14 * 60 + 30), # 9:30 to 14:30
        (15 * 60, 15 * 60 + 30),     # 15:00 to 15:30
        (16 * 60, 17 * 60)          # 16:00 to 17:00
    ]
}

# Soft Constraints (preferences):
# Kelly would like to avoid meeting on Wednesday (day 2) or Friday (day 4).
def compute_penalty(d):
    penalty = 0
    penalty += If(d == 2, 1, 0)  # penalty for Wednesday
    penalty += If(d == 4, 1, 0)  # penalty for Friday
    return penalty

# Helper function: meeting interval [s, s+duration) should not overlap with blocked interval [bstart, bend)
def no_overlap(s, duration, bstart, bend):
    return Or(s + duration <= bstart, s >= bend)

# Create an optimizer
opt = Optimize()

# Variables:
# d: meeting day (0=Monday, ..., 4=Friday)
# s: meeting start time in minutes (from midnight)
d = Int("d")
s = Int("s")

# Basic constraints: day is between 0 and 4, and meeting is within working hours.
opt.add(d >= 0, d <= 4)
opt.add(s >= WORK_START, s + duration <= WORK_END)

# Hard constraints for Kelly:
for day in kelly_busy:
    for (bstart, bend) in kelly_busy[day]:
        # If the meeting is on 'day', then ensure no overlap with Kelly's busy interval.
        opt.add(If(d == day, no_overlap(s, duration, bstart, bend), True))

# Hard constraints for Bobby:
for day in bobby_busy:
    for (bstart, bend) in bobby_busy[day]:
        # If the meeting is on 'day', ensure no overlap with Bobby's busy interval.
        opt.add(If(d == day, no_overlap(s, duration, bstart, bend), True))

# Add soft objective: minimize penalty for Kelly's preferences.
penalty = compute_penalty(d)
opt.minimize(penalty)

# Secondary objective: try to schedule as early as possible 
# (i.e. lower day value, and for same day, lower start time).
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