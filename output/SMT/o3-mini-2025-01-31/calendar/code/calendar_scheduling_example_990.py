from z3 import Optimize, Int, If, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes
WORK_START = 9 * 60   # 9:00 in minutes (540)
WORK_END = 17 * 60    # 17:00 in minutes (1020)

# Map days: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Sean's busy schedule (in minutes)
# Monday: 11:00-11:30
# Thursday: 10:00-10:30, 11:00-11:30, 15:00-15:30
# Friday: 9:00-9:30, 10:30-11:00
sean_busy = {
    0: [(11 * 60, 11 * 60 + 30)],
    3: [(10 * 60, 10 * 60 + 30), (11 * 60, 11 * 60 + 30), (15 * 60, 15 * 60 + 30)],
    4: [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 11 * 60)]
}
# Sean is free on Tuesday and Wednesday.

# Michelle's busy schedule (in minutes)
# Monday: 9:00-9:30, 10:00-14:00, 14:30-17:00
# Tuesday: 9:00-17:00
# Wednesday: 9:30-10:00, 11:30-12:00, 12:30-15:30, 16:00-17:00
# Thursday: 9:00-13:00, 13:30-16:30
# Friday: 9:00-9:30, 10:00-13:00, 13:30-17:00
michelle_busy = {
    0: [(9 * 60, 9 * 60 + 30), (10 * 60, 14 * 60), (14 * 60 + 30, 17 * 60)],
    1: [(9 * 60, 17 * 60)],
    2: [(9 * 60 + 30, 10 * 60), (11 * 60 + 30, 12 * 60), (12 * 60 + 30, 15 * 60 + 30), (16 * 60, 17 * 60)],
    3: [(9 * 60, 13 * 60), (13 * 60 + 30, 16 * 60 + 30)],
    4: [(9 * 60, 9 * 60 + 30), (10 * 60, 13 * 60), (13 * 60 + 30, 17 * 60)]
}

# Helper: meeting at start with duration must not overlap busy interval [busy_start, busy_end)
def no_overlap(start, duration, busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Create the Z3 optimizer
opt = Optimize()

# Decision variables:
# d: day index (0=Monday,...,4=Friday)
# s: meeting start time (in minutes after midnight)
d = Int("d")
s = Int("s")

# Meeting must occur entirely within work hours.
opt.add(s >= WORK_START, s + duration <= WORK_END)
opt.add(d >= 0, d <= 4)

# Add constraints for Sean's busy times.
for day, intervals in sean_busy.items():
    for (busy_start, busy_end) in intervals:
        # If meeting is on that day then it must not overlap Sean's busy time.
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Add constraints for Michelle's busy times.
for day, intervals in michelle_busy.items():
    for (busy_start, busy_end) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Soft preferences:
# Sean would like to avoid meetings on Monday
# Sean would like to avoid meetings on Thursday after 16:30 (16:30 = 16*60 + 30 = 990 minutes)
# Michelle would like to avoid meetings on Wednesday and Friday.
penalty = 0
penalty += If(d == 0, 1, 0)                     # Monday penalty for Sean.
penalty += If(And(d == 3, s >= (16 * 60 + 30)), 1, 0)  # Thursday after 16:30 penalty for Sean.
penalty += If(d == 2, 1, 0)                     # Wednesday penalty for Michelle.
penalty += If(d == 4, 1, 0)                     # Friday penalty for Michelle.

# First, minimize penalties, then try for the earliest meeting time.
opt.minimize(penalty)
opt.minimize(d * WORK_END + s)

# Check for a solution and display it.
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