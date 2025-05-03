from z3 import Optimize, Int, If, Or, sat

# Meeting parameters
duration = 60               # one hour meeting (in minutes)
WORK_START = 9 * 60         # 9:00 AM -> 540 minutes
WORK_END   = 17 * 60        # 17:00 -> 1020 minutes

# Days: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Michael's busy intervals by day (in minutes after midnight)
michael_busy = {
    0: [  # Monday
        (16 * 60 + 30, 17 * 60)  # 16:30 to 17:00
    ],
    1: [  # Tuesday
        (10 * 60, 10 * 60 + 30),   # 10:00 to 10:30
        (11 * 60 + 30, 12 * 60),   # 11:30 to 12:00
        (13 * 60 + 30, 14 * 60),   # 13:30 to 14:00
        (15 * 60 + 30, 16 * 60)    # 15:30 to 16:00
    ],
    2: [  # Wednesday
        (10 * 60 + 30, 11 * 60),   # 10:30 to 11:00
        (11 * 60 + 30, 12 * 60)    # 11:30 to 12:00
    ],
    3: [  # Thursday
        (10 * 60, 11 * 60 + 30)    # 10:00 to 11:30
    ]
    # Friday: Michael has no meetings.
}

# Justin's busy intervals by day (in minutes)
justin_busy = {
    0: [  # Monday
        (9 * 60, 11 * 60),         # 9:00 to 11:00
        (11 * 60 + 30, 13 * 60),    # 11:30 to 13:00
        (14 * 60, 14 * 60 + 30),    # 14:00 to 14:30
        (15 * 60 + 30, 16 * 60),    # 15:30 to 16:00
        (16 * 60 + 30, 17 * 60)     # 16:30 to 17:00
    ],
    1: [  # Tuesday
        (9 * 60, 17 * 60)          # Busy all day (9:00 to 17:00)
    ],
    2: [  # Wednesday
        (10 * 60 + 30, 11 * 60),    # 10:30 to 11:00
        (12 * 60 + 30, 14 * 60 + 30),# 12:30 to 14:30
        (15 * 60, 15 * 60 + 30),     # 15:00 to 15:30
        (16 * 60 + 30, 17 * 60)      # 16:30 to 17:00
    ],
    3: [  # Thursday
        (9 * 60, 10 * 60),         # 9:00 to 10:00
        (12 * 60 + 30, 13 * 60),    # 12:30 to 13:00
        (14 * 60 + 30, 15 * 60),    # 14:30 to 15:00
        (16 * 60, 17 * 60)         # 16:00 to 17:00
    ],
    4: [  # Friday
        (9 * 60, 10 * 60 + 30),     # 9:00 to 10:30
        (11 * 60, 11 * 60 + 30),    # 11:00 to 11:30
        (12 * 60, 14 * 60 + 30),     # 12:00 to 14:30
        (15 * 60, 17 * 60)          # 15:00 to 17:00
    ]
}

# Helper function:
# Given a meeting starting at time s (minutes), lasting "duration", 
# and a busy interval [bstart, bend),
# return the constraint that the meeting and busy interval do not overlap.
def no_overlap(s, duration, bstart, bend):
    return Or(s + duration <= bstart, s >= bend)

# Create the Z3 Optimize solver (allows for optimization objectives)
opt = Optimize()

# Decision variables:
# d: meeting day (0..4)
# s: meeting start time (in minutes, from midnight)
d = Int("d")
s = Int("s")

# Enforce meeting within working hours.
opt.add(s >= WORK_START, s + duration <= WORK_END)
opt.add(d >= 0, d <= 4)

# Participant-specific day preferences / constraints:
# Justin does not want to meet on Monday.
opt.add(d != 0)

# Michael has an additional constraint: 
# - If meeting is on Wednesday, the meeting should not start before 10:30.
# - Also, Michael cannot meet on Thursday.
opt.add(If(d == 2, s >= 10 * 60 + 30, True))  # Wednesday: s >= 10:30
opt.add(d != 3)  # Michael cannot meet on Thursday

# Add Michael's busy constraints.
for day, intervals in michael_busy.items():
    for (bstart, bend) in intervals:
        # Apply constraint only if meeting is on the specific day.
        opt.add(If(d == day, no_overlap(s, duration, bstart, bend), True))

# Add Justin's busy constraints.
for day, intervals in justin_busy.items():
    for (bstart, bend) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, bstart, bend), True))

# Soft objective: choose the earliest available meeting time.
# We define "earliest" by combining the day and start time.
earliest_expr = d * WORK_END + s
opt.minimize(earliest_expr)

# Check and print the solution.
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