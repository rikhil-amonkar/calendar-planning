from z3 import Optimize, Int, If, Or, And, sat

# Meeting parameters
duration = 30  # meeting duration in minutes (30 minutes)
WORK_START = 9 * 60   # 9:00 in minutes (540)
WORK_END = 17 * 60    # 17:00 in minutes (1020)

# Map days: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Kelly's busy schedule (times in minutes)
# Monday: 9:30-10:00, 11:30-12:00, 14:00-14:30, 15:00-15:30
# Tuesday: 9:30-10:00, 10:30-11:00, 14:00-14:30
# Wednesday: 10:30-12:00, 13:00-13:30, 14:00-14:30, 15:30-16:00
# Thursday: 9:00-10:30, 11:30-12:00, 14:30-15:00, 15:30-16:00
# Friday: 9:00-9:30, 14:30-15:00, 16:30-17:00
kelly_busy = {
    0: [(9 * 60 + 30, 10 * 60), (11 * 60 + 30, 12 * 60),
        (14 * 60, 14 * 60 + 30), (15 * 60, 15 * 60 + 30)],
    1: [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 11 * 60),
        (14 * 60, 14 * 60 + 30)],
    2: [(10 * 60 + 30, 12 * 60), (13 * 60, 13 * 60 + 30),
        (14 * 60, 14 * 60 + 30), (15 * 60 + 30, 16 * 60)],
    3: [(9 * 60, 10 * 60 + 30), (11 * 60 + 30, 12 * 60),
        (14 * 60 + 30, 15 * 60), (15 * 60 + 30, 16 * 60)],
    4: [(9 * 60, 9 * 60 + 30), (14 * 60 + 30, 15 * 60), (16 * 60 + 30, 17 * 60)]
}

# Nathan's busy schedule (times in minutes)
# Monday: 9:00-9:30, 10:00-11:30, 13:00-15:30, 16:00-17:00
# Tuesday: 9:00-17:00
# Wednesday: 9:00-16:00, 16:30-17:00
# Thursday: 9:00-17:00
# Friday: 9:00-17:00
nathan_busy = {
    0: [(9 * 60, 9 * 60 + 30), (10 * 60, 11 * 60 + 30),
        (13 * 60, 15 * 60 + 30), (16 * 60, 17 * 60)],
    1: [(9 * 60, 17 * 60)],
    2: [(9 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)],
    3: [(9 * 60, 17 * 60)],
    4: [(9 * 60, 17 * 60)]
}

# Helper function: ensure meeting starting at 'start' with length 'duration'
# does not overlap a busy interval [busy_start, busy_end)
def no_overlap(start, duration, busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Create the Z3 optimizer
opt = Optimize()

# Decision variables:
# d: day of the meeting, 0-4 corresponding to Monday-Friday
# s: meeting start time in minutes after midnight
d = Int("d")
s = Int("s")

# The meeting must be within work hours.
opt.add(s >= WORK_START, s + duration <= WORK_END)
opt.add(d >= 0, d <= 4)

# Add Kelly's busy constraints
for day, intervals in kelly_busy.items():
    for busy_start, busy_end in intervals:
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Add Nathan's busy constraints
for day, intervals in nathan_busy.items():
    for busy_start, busy_end in intervals:
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Preference:
# Kelly would rather not meet on Monday (day 0).
penalty = If(d == 0, 1, 0)

# Objectives: first minimize penalty, then schedule at earliest possible time.
opt.minimize(penalty)
opt.minimize(d * WORK_END + s)

# Solve and output the scheduled meeting time.
if opt.check() == sat:
    model = opt.model()
    chosen_day = model[d].as_long()
    meeting_start = model[s].as_long()
    meeting_end = meeting_start + duration
    start_hour, start_min = divmod(meeting_start, 60)
    end_hour, end_min = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
          day_names[chosen_day], start_hour, start_min, end_hour, end_min))
else:
    print("No valid meeting time found.")