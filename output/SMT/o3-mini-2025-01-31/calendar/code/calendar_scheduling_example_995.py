from z3 import Optimize, Int, If, Or, And, sat

# Meeting parameters
duration = 60  # meeting duration in minutes (1 hour)
WORK_START = 9 * 60   # 9:00 AM in minutes (540)
WORK_END = 17 * 60    # 5:00 PM in minutes (1020)

# Map days: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Bruce's busy schedule (times in minutes)
# Monday: 12:00-12:30, 13:00-14:00, 16:00-16:30
# Tuesday: 9:30-10:00, 11:00-12:00
# Wednesday: 14:00-15:00, 15:30-16:00
# Thursday: 9:00-10:00, 12:00-12:30, 14:00-14:30
# Friday: 11:00-11:30, 14:00-15:00, 16:30-17:00
bruce_busy = {
    0: [(12 * 60, 12 * 60 + 30), (13 * 60, 14 * 60), (16 * 60, 16 * 60 + 30)],
    1: [(9 * 60 + 30, 10 * 60), (11 * 60, 12 * 60)],
    2: [(14 * 60, 15 * 60), (15 * 60 + 30, 16 * 60)],
    3: [(9 * 60, 10 * 60), (12 * 60, 12 * 60 + 30), (14 * 60, 14 * 60 + 30)],
    4: [(11 * 60, 11 * 60 + 30), (14 * 60, 15 * 60), (16 * 60 + 30, 17 * 60)]
}

# Heather's busy schedule (times in minutes)
# Monday: 11:30-12:30, 13:00-13:30, 15:30-16:00, 16:30-17:00
# Tuesday: 9:00-11:30, 12:00-12:30, 13:00-15:00, 15:30-17:00
# Wednesday: 10:00-11:30, 12:30-13:30, 15:30-17:00
# Thursday: 9:30-11:00, 11:30-14:30, 15:00-15:30, 16:00-17:00
# Friday: 11:30-12:30, 13:00-13:30, 15:00-16:00, 16:30-17:00
heather_busy = {
    0: [(11 * 60 + 30, 12 * 60 + 30), (13 * 60, 13 * 60 + 30),
        (15 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)],
    1: [(9 * 60, 11 * 60 + 30), (12 * 60, 12 * 60 + 30),
        (13 * 60, 15 * 60), (15 * 60 + 30, 17 * 60)],
    2: [(10 * 60, 11 * 60 + 30), (12 * 60 + 30, 13 * 60 + 30),
        (15 * 60 + 30, 17 * 60)],
    3: [(9 * 60 + 30, 11 * 60), (11 * 60 + 30, 14 * 60 + 30),
        (15 * 60, 15 * 60 + 30), (16 * 60, 17 * 60)],
    4: [(11 * 60 + 30, 12 * 60 + 30), (13 * 60, 13 * 60 + 30),
        (15 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)]
}

# Helper function: ensures that a meeting starting at 'start' with duration 'duration'
# does not overlap a busy time interval [busy_start, busy_end)
def no_overlap(start, duration, busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Create the Z3 optimizer
opt = Optimize()

# Decision variables:
# d: day of the meeting (0-4 representing Monday to Friday)
# s: meeting start time in minutes after midnight
d = Int("d")
s = Int("s")

# Constraint: the meeting must be within work hours.
opt.add(s >= WORK_START, s + duration <= WORK_END)
opt.add(d >= 0, d <= 4)

# Add Bruce's busy constraints for his scheduled intervals.
for day, intervals in bruce_busy.items():
    for busy_start, busy_end in intervals:
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Add Heather's busy constraints for her scheduled intervals.
for day, intervals in heather_busy.items():
    for busy_start, busy_end in intervals:
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Preferences:
# Bruce would rather not meet on Wednesday (day 2).
# Heather would like to avoid meetings on Monday after 12:30 (s >= 12:30 on day 0) and avoid Friday.
penalty = 0
penalty += If(d == 2, 1, 0)  # Bruce penalty for Wednesday (day 2)
penalty += If(And(d == 0, s >= (12 * 60 + 30)), 1, 0)  # Heather penalty for Monday after 12:30
penalty += If(d == 4, 1, 0)  # Heather penalty for Friday (day 4)

# Objectives: minimize penalty first, then minimize the meeting start time in the week (earlier is better).
opt.minimize(penalty)
opt.minimize(d * WORK_END + s)

# Solve and print the scheduled meeting time.
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