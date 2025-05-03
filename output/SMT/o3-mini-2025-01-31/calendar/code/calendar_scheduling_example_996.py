from z3 import Optimize, Int, If, Or, sat

# Meeting parameters
duration = 60  # meeting duration in minutes (1 hour)
WORK_START = 9 * 60   # 9:00 AM in minutes (540)
WORK_END = 17 * 60    # 5:00 PM in minutes (1020)

# Map days: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Lauren's schedule: free all week (no busy intervals)

# Willie's busy schedule (times in minutes)
# Monday: 9:00-13:00, 14:00-17:00
# Tuesday: 9:00-17:00
# Wednesday: 9:00-11:30, 12:00-17:00
# Thursday: 9:00-16:00, 16:30-17:00
# Friday: 9:00-17:00
willie_busy = {
    0: [(9 * 60, 13 * 60), (14 * 60, 17 * 60)],
    1: [(9 * 60, 17 * 60)],
    2: [(9 * 60, 11 * 60 + 30), (12 * 60, 17 * 60)],
    3: [(9 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)],
    4: [(9 * 60, 17 * 60)]
}

# Helper function:
# This function returns constraints ensuring that a meeting starting at 'start' with duration 'duration'
# does not overlap with a busy interval [busy_start, busy_end).
def no_overlap(start, duration, busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Create the Z3 optimizer
opt = Optimize()

# Decision variables:
# d: day of the meeting (0 for Monday, ... 4 for Friday)
# s: meeting start time in minutes (after midnight)
d = Int("d")
s = Int("s")

# Constraint: the meeting must occur within work hours.
opt.add(s >= WORK_START, s + duration <= WORK_END)
opt.add(d >= 0, d <= 4)

# Add Willie's busy constraints:
# For each busy interval on a day, if the meeting is on that day, then the meeting must not overlap that interval.
for day, intervals in willie_busy.items():
    for (busy_start, busy_end) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# No additional constraints from Lauren since she is free.

# Objective: Pick the earliest available meeting time.
opt.minimize(d * WORK_END + s)

# Solve and display the scheduled meeting time.
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