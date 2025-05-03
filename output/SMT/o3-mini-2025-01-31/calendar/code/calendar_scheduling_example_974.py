from z3 import Optimize, Int, If, Or, sat

# Meeting parameters
duration = 60               # one hour meeting
WORK_START = 9 * 60         # 9:00 AM in minutes (540)
WORK_END = 17 * 60          # 17:00 in minutes (1020)

# Map numeric day to day names: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Donald's busy times by day (times in minutes from midnight)
donald_busy = {
    0: [  # Monday
        (9 * 60, 9 * 60 + 30)    # 9:00-9:30
    ],
    1: [  # Tuesday
        (11 * 60, 11 * 60 + 30),  # 11:00-11:30
        (15 * 60, 15 * 60 + 30)   # 15:00-15:30
    ],
    3: [  # Thursday
        (14 * 60 + 30, 15 * 60)   # 14:30-15:00
    ]
    # Wednesday (2) and Friday (4) are free for Donald
}

# Emily's busy times by day (times in minutes from midnight)
emily_busy = {
    0: [  # Monday
        (9 * 60, 9 * 60 + 30),       # 9:00-9:30
        (10 * 60, 12 * 60 + 30),      # 10:00-12:30
        (13 * 60, 13 * 60 + 30),      # 13:00-13:30
        (14 * 60, 14 * 60 + 30),      # 14:00-14:30
        (15 * 60, 16 * 60)           # 15:00-16:00
    ],
    1: [  # Tuesday
        (9 * 60, 10 * 60 + 30),      # 9:00-10:30
        (11 * 60, 12 * 60 + 30),     # 11:00-12:30
        (13 * 60, 16 * 60),          # 13:00-16:00
        (16 * 60 + 30, 17 * 60)      # 16:30-17:00
    ],
    2: [  # Wednesday
        (9 * 60, 9 * 60 + 30),       # 9:00-9:30
        (10 * 60, 10 * 60 + 30),     # 10:00-10:30
        (11 * 60, 12 * 60),          # 11:00-12:00
        (14 * 60, 15 * 60 + 30),     # 14:00-15:30
        (16 * 60, 16 * 60 + 30)      # 16:00-16:30
    ],
    3: [  # Thursday
        (9 * 60 + 30, 11 * 60),      # 9:30-11:00
        (11 * 60 + 30, 13 * 60),     # 11:30-13:00
        (13 * 60 + 30, 16 * 60 + 30)  # 13:30-16:30
    ],
    4: [  # Friday
        (9 * 60 + 30, 11 * 60 + 30), # 9:30-11:30
        (12 * 60, 12 * 60 + 30),      # 12:00-12:30
        (13 * 60 + 30, 14 * 60),      # 13:30-14:00
        (14 * 60 + 30, 17 * 60)       # 14:30-17:00
    ]
}

# Helper function: a meeting with start time 's' lasting 'duration' does not overlap a busy interval (bstart, bend)
def no_overlap(s, duration, bstart, bend):
    return Or(s + duration <= bstart, s >= bend)

# Create an Optimize instance
opt = Optimize()

# Define decision variables:
# d: day of meeting (0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday)
# s: meeting start time in minutes from midnight
d = Int("d")
s = Int("s")

# Meeting must be within working hours.
opt.add(s >= WORK_START, s + duration <= WORK_END)
opt.add(d >= 0, d <= 4)

# Add participant day constraints:
# Donald cannot meet on Monday -> d != 0.
# Emily does not want to meet on Wednesday -> d != 2.
opt.add(d != 0, d != 2)

# Now add busy time constraints for Donald
for day, intervals in donald_busy.items():
    for (bstart, bend) in intervals:
        # Only add constraint if meeting is on that day
        opt.add(If(d == day, no_overlap(s, duration, bstart, bend), True))

# Add busy time constraints for Emily
for day, intervals in emily_busy.items():
    for (bstart, bend) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, bstart, bend), True))

# Soft objective: schedule the meeting at the earliest possible time.
# We define "earliest" as minimizing d * WORK_END + s. (Days are weighted by work_end minutes.)
earliest_expr = d * WORK_END + s
opt.minimize(earliest_expr)

# Check if constraints are satisfied and display the result
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