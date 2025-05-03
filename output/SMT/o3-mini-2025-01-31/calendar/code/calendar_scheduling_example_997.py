from z3 import Optimize, Int, If, Or, sat

# Meeting parameters
duration = 30  # duration in minutes
WORK_START = 9 * 60   # 9:00 in minutes (540)
WORK_END = 17 * 60    # 17:00 in minutes (1020)

# Map days: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Stephanie is free all week

# Ashley's busy schedule in minutes:
# Monday: 9:30-10:00, 12:00-12:30, 13:00-13:30, 16:00-17:00
# Tuesday: 9:00-9:30, 10:30-13:00, 14:30-16:00
# Wednesday: 9:00-10:00, 10:30-11:30, 13:00-14:00, 16:30-17:00
# Thursday: 9:00-9:30, 10:30-11:00, 11:30-14:30, 15:00-16:00, 16:30-17:00
# Friday: 9:30-12:00, 13:30-14:30, 15:00-15:30
ashley_busy = {
    0: [(9 * 60 + 30, 10 * 60), (12 * 60, 12 * 60 + 30),
        (13 * 60, 13 * 60 + 30), (16 * 60, 17 * 60)],
    1: [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 13 * 60),
        (14 * 60 + 30, 16 * 60)],
    2: [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60 + 30),
        (13 * 60, 14 * 60), (16 * 60 + 30, 17 * 60)],
    3: [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 11 * 60),
        (11 * 60 + 30, 14 * 60 + 30), (15 * 60, 16 * 60),
        (16 * 60 + 30, 17 * 60)],
    4: [(9 * 60 + 30, 12 * 60), (13 * 60 + 30, 14 * 60 + 30),
        (15 * 60, 15 * 60 + 30)]
}

# Helper function:
# Ensures that a meeting starting at 'start' with duration 'duration'
# does not overlap with a busy interval [busy_start, busy_end).
def no_overlap(start, duration, busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Create the Z3 optimizer
opt = Optimize()

# Decision variables:
# d: day (0 to 4) and s: meeting start time (in minutes) on that day.
d = Int("d")
s = Int("s")

# Meeting within work hours constraints:
opt.add(s >= WORK_START, s + duration <= WORK_END)
opt.add(d >= 0, d <= 4)

# Add Ashley's busy constraints:
for day, intervals in ashley_busy.items():
    for (busy_start, busy_end) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Preferences:
# Ashley would like to avoid more meetings on Monday (day 0) and Thursday (day 3).
penalty = 0
penalty += If(d == 0, 1, 0)
penalty += If(d == 3, 1, 0)

# Objective: minimize penalty then choose the earliest meeting time.
opt.minimize(penalty)
opt.minimize(d * WORK_END + s)  # earlier overall time gets priority

# Solve and print the meeting time
if opt.check() == sat:
    model = opt.model()
    chosen_day = model[d].as_long()
    meeting_start = model[s].as_long()
    meeting_end = meeting_start + duration
    sh, sm = divmod(meeting_start, 60)
    eh, em = divmod(meeting_end, 60)
    print("Meeting scheduled on {} from {:02d}:{:02d} to {:02d}:{:02d}".format(
          day_names[chosen_day], sh, sm, eh, em))
else:
    print("No valid meeting time found.")