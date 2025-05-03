from z3 import Optimize, Int, If, Or, sat

# Meeting parameters
duration = 30               # half an hour meeting
WORK_START = 9 * 60         # 9:00 AM in minutes (540)
WORK_END = 17 * 60          # 17:00 in minutes (1020)

# Mapping days: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Jordan's busy times (in minutes) by day
jordan_busy = {
    0: [  # Monday
        (10 * 60 + 30, 11 * 60),   # 10:30-11:00
        (11 * 60 + 30, 12 * 60),   # 11:30-12:00
        (12 * 60 + 30, 13 * 60),   # 12:30-13:00
        (13 * 60 + 30, 14 * 60),   # 13:30-14:00
        (14 * 60 + 30, 15 * 60),   # 14:30-15:00
        (15 * 60 + 30, 16 * 60),   # 15:30-16:00
        (16 * 60 + 30, 17 * 60)    # 16:30-17:00
    ],
    1: [  # Tuesday
        (9 * 60, 10 * 60),         # 9:00-10:00
        (10 * 60 + 30, 11 * 60),    # 10:30-11:00
        (12 * 60 + 30, 13 * 60 + 30),# 12:30-13:30
        (14 * 60, 14 * 60 + 30),    # 14:00-14:30
        (15 * 60, 15 * 60 + 30)     # 15:00-15:30
    ],
    2: [  # Wednesday
        (10 * 60, 10 * 60 + 30),    # 10:00-10:30
        (13 * 60 + 30, 14 * 60 + 30),# 13:30-14:30
        (15 * 60 + 30, 16 * 60)     # 15:30-16:00
    ],
    3: [  # Thursday
        (9 * 60, 9 * 60 + 30),      # 9:00-9:30
        (14 * 60, 14 * 60 + 30),    # 14:00-14:30
        (15 * 60, 15 * 60 + 30)     # 15:00-15:30
    ],
    4: [  # Friday
        (9 * 60, 9 * 60 + 30),      # 9:00-9:30
        (11 * 60, 11 * 60 + 30),    # 11:00-11:30
        (12 * 60, 12 * 60 + 30),    # 12:00-12:30
        (15 * 60, 16 * 60)          # 15:00-16:00
    ]
}

# Alice's busy times (in minutes) by day
alice_busy = {
    0: [  # Monday
        (9 * 60, 9 * 60 + 30),      # 9:00-9:30
        (10 * 60, 11 * 60),         # 10:00-11:00
        (12 * 60, 15 * 60),         # 12:00-15:00
        (15 * 60 + 30, 17 * 60)     # 15:30-17:00
    ],
    1: [  # Tuesday
        (9 * 60, 9 * 60 + 30),      # 9:00-9:30
        (10 * 60, 10 * 60 + 30),    # 10:00-10:30
        (11 * 60, 12 * 60),         # 11:00-12:00
        (12 * 60 + 30, 14 * 60 + 30),# 12:30-14:30
        (15 * 60, 15 * 60 + 30)     # 15:00-15:30
    ],
    2: [  # Wednesday
        (9 * 60 + 30, 11 * 60 + 30),# 9:30-11:30
        (13 * 60, 13 * 60 + 30),    # 13:00-13:30
        (14 * 60, 15 * 60 + 30)     # 14:00-15:30
    ],
    3: [  # Thursday
        (9 * 60, 10 * 60 + 30),     # 9:00-10:30
        (11 * 60 + 30, 12 * 60 + 30),# 11:30-12:30
        (13 * 60 + 30, 14 * 60),     # 13:30-14:00
        (15 * 60, 16 * 60)          # 15:00-16:00
    ],
    4: [  # Friday
        (9 * 60, 10 * 60),          # 9:00-10:00
        (12 * 60, 12 * 60 + 30),     # 12:00-12:30
        (13 * 60, 13 * 60 + 30),     # 13:00-13:30
        (14 * 60, 14 * 60 + 30),     # 14:00-14:30
        (15 * 60, 16 * 60)          # 15:00-16:00
    ]
}

# Helper function to enforce no overlap between meeting [s, s+duration) and a busy interval [bstart, bend).
def no_overlap(s, duration, bstart, bend):
    return Or(s + duration <= bstart, s >= bend)

# Create an Optimize instance
opt = Optimize()

# Define decision variables
# d: day of the meeting (0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday)
# s: meeting start time (in minutes from midnight)
d = Int("d")
s = Int("s")

# Basic working-hours constraint
opt.add(s >= WORK_START, s + duration <= WORK_END)

# Additional availability constraints from participants:
# Jordan cannot meet on Monday, Wednesday, or Thursday;
# => Allowed days for Jordan: Tuesday (1) or Friday (4)
# Alice does not want to meet on Tuesday.
# => Thus the only feasible day is Friday.
opt.add(d == 4)

# Additional constraint for Alice:
# On Friday, Alice does not want meetings scheduled after 11:30.
# Given a 30-minute meeting, it must finish by 11:30.
opt.add(s + duration <= (11 * 60 + 30))  # i.e., s + 30 <= 690

# Add day constraint (though d is already fixed to 4, we include 0<=d<=4 for formality)
opt.add(d >= 0, d <= 4)

# Add constraints for Jordan's busy times
for day, intervals in jordan_busy.items():
    for (bstart, bend) in intervals:
        # Add constraint only if meeting is on that day.
        opt.add(If(d == day, no_overlap(s, duration, bstart, bend), True))

# Add constraints for Alice's busy times
for day, intervals in alice_busy.items():
    for (bstart, bend) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, bstart, bend), True))

# Soft objective: schedule at the earliest availability.
# Define "earliest" as minimizing d * WORK_END + s.
# Since d is forced to Friday (4), this minimizes s.
earliest_expr = d * WORK_END + s
opt.minimize(earliest_expr)

# Check the constraints and print the result if available
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