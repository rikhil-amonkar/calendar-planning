from z3 import Optimize, Int, If, Or, And, sat

# Meeting parameters
duration = 60  # meeting duration in minutes (1 hour)
WORK_START = 9 * 60   # 9:00 AM expressed in minutes (540)
WORK_END = 17 * 60    # 5:00 PM expressed in minutes (1020)

# Map days: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# William's busy schedule (times are in minutes)
# Monday: 10:00-10:30, 11:00-11:30, 12:30-13:00
# Tuesday: 14:00-14:30, 15:30-16:00
# Thursday: 9:30-10:00, 13:00-14:00, 15:00-15:30
# Friday: 11:00-11:30
william_busy = {
    0: [(10 * 60, 10 * 60 + 30), (11 * 60, 11 * 60 + 30), (12 * 60 + 30, 13 * 60)],
    1: [(14 * 60, 14 * 60 + 30), (15 * 60 + 30, 16 * 60)],
    3: [(9 * 60 + 30, 10 * 60), (13 * 60, 14 * 60), (15 * 60, 15 * 60 + 30)],
    4: [(11 * 60, 11 * 60 + 30)]
}

# Nancy's busy schedule (times in minutes)
# Monday: 10:00-10:30, 12:00-12:30, 14:30-15:00, 15:30-16:00
# Tuesday: 9:30-10:00, 11:00-12:00, 13:00-13:30, 14:00-15:00, 15:30-16:00
# Wednesday: 9:30-10:30, 11:00-12:30, 14:00-14:30, 15:00-15:30, 16:30-17:00
# Thursday: 9:00-10:00, 11:00-11:30, 12:00-17:00
# Friday: 9:00-9:30, 10:00-11:30, 12:00-13:00, 14:00-14:30, 15:00-15:30, 16:00-17:00
nancy_busy = {
    0: [(10 * 60, 10 * 60 + 30), (12 * 60, 12 * 60 + 30),
        (14 * 60 + 30, 15 * 60), (15 * 60 + 30, 16 * 60)],
    1: [(9 * 60 + 30, 10 * 60), (11 * 60, 12 * 60),
        (13 * 60, 13 * 60 + 30), (14 * 60, 15 * 60), (15 * 60 + 30, 16 * 60)],
    2: [(9 * 60 + 30, 10 * 60 + 30), (11 * 60, 12 * 60 + 30),
        (14 * 60, 14 * 60 + 30), (15 * 60, 15 * 60 + 30), (16 * 60 + 30, 17 * 60)],
    3: [(9 * 60, 10 * 60), (11 * 60, 11 * 60 + 30), (12 * 60, 17 * 60)],
    4: [(9 * 60, 9 * 60 + 30), (10 * 60, 11 * 60 + 30), (12 * 60, 13 * 60),
        (14 * 60, 14 * 60 + 30), (15 * 60, 15 * 60 + 30), (16 * 60, 17 * 60)]
}

# Helper function: no_overlap ensures the meeting (starting at 'start' with duration 'duration')
# does not overlap with a busy interval [busy_start, busy_end)
def no_overlap(start, duration, busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Create the Z3 optimizer
opt = Optimize()

# Decision variables:
# d: day of the meeting (integer 0-4 corresponding to Monday-Friday)
# s: meeting start time in minutes after midnight
d = Int("d")
s = Int("s")

# Meeting must occur within work hours.
opt.add(s >= WORK_START, s + duration <= WORK_END)
opt.add(d >= 0, d <= 4)

# William's busy intervals constraints
for day, intervals in william_busy.items():
    for (busy_start, busy_end) in intervals:
        # If the meeting is on this day, then the meeting must not overlap the busy interval.
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Nancy's busy intervals constraints
for day, intervals in nancy_busy.items():
    for (busy_start, busy_end) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Preferences:
# Nancy would rather not meet on Tuesday (day 1) and Friday (day 4)
penalty = 0
penalty += If(d == 1, 1, 0)  # penalty for Tuesday
penalty += If(d == 4, 1, 0)  # penalty for Friday

# Define objective: first minimize the penalty, then schedule at earliest availability.
opt.minimize(penalty)
opt.minimize(d * WORK_END + s)

# Solve and display the meeting time.
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