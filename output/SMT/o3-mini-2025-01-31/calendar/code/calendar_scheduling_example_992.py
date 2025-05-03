from z3 import Optimize, Int, If, Or, And, sat

# Meeting parameters
duration = 30  # 30-minute meeting
WORK_START = 9 * 60   # 9:00 AM in minutes (540)
WORK_END = 17 * 60    # 5:00 PM in minutes (1020)

# Map days: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Walter's busy schedule (times in minutes)
# Monday: 9:30-10:00, 10:30-13:00, 13:30-14:00
# Tuesday: 9:00-10:30, 12:00-13:30, 16:30-17:00
# Wednesday: 11:30-13:00, 14:00-14:30, 16:30-17:00
# Thursday: 9:30-11:30, 12:00-12:30, 14:00-15:00, 16:30-17:00
# Friday: 9:00-9:30, 11:30-13:00, 13:30-14:00, 14:30-15:00, 15:30-16:00
walter_busy = {
    0: [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 13 * 60), (13 * 60 + 30, 14 * 60)],
    1: [(9 * 60, 10 * 60 + 30), (12 * 60, 13 * 60 + 30), (16 * 60 + 30, 17 * 60)],
    2: [(11 * 60 + 30, 13 * 60), (14 * 60, 14 * 60 + 30), (16 * 60 + 30, 17 * 60)],
    3: [(9 * 60 + 30, 11 * 60 + 30), (12 * 60, 12 * 60 + 30), (14 * 60, 15 * 60), (16 * 60 + 30, 17 * 60)],
    4: [(9 * 60, 9 * 60 + 30), (11 * 60 + 30, 13 * 60), (13 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60), (15 * 60 + 30, 16 * 60)]
}

# Grace's busy schedule (times in minutes)
# Monday: 9:00-10:00, 11:30-15:30, 16:00-16:30
# Tuesday: 9:00-13:30, 14:00-15:00, 15:30-16:00, 16:30-17:00
# Wednesday: 10:30-11:00, 11:30-12:00, 12:30-13:30, 14:00-16:00, 16:30-17:00
# Thursday: 10:30-11:30
# Friday: 9:00-10:30, 11:00-12:30, 13:00-15:00, 15:30-17:00
grace_busy = {
    0: [(9 * 60, 10 * 60), (11 * 60 + 30, 15 * 60 + 30), (16 * 60, 16 * 60 + 30)],
    1: [(9 * 60, 13 * 60 + 30), (14 * 60, 15 * 60), (15 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)],
    2: [(10 * 60 + 30, 11 * 60), (11 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60 + 30),
        (14 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)],
    3: [(10 * 60 + 30, 11 * 60 + 30)],
    4: [(9 * 60, 10 * 60 + 30), (11 * 60, 12 * 60 + 30), (13 * 60, 15 * 60), (15 * 60 + 30, 17 * 60)]
}

# Helper function: Ensure that a meeting starting at 'start' with 'duration'
# does not overlap a busy interval [busy_start, busy_end)
def no_overlap(start, duration, busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Create the Z3 optimizer
opt = Optimize()

# Decision variables:
# d: day index (0 for Monday, ..., 4 for Friday)
# s: meeting start time in minutes after midnight
d = Int("d")
s = Int("s")

# Constraint: meeting must be within work hours
opt.add(s >= WORK_START, s + duration <= WORK_END)
opt.add(d >= 0, d <= 4)

# Add Walter's busy constraints
for day, intervals in walter_busy.items():
    for (busy_start, busy_end) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Add Grace's busy constraints
for day, intervals in grace_busy.items():
    for (busy_start, busy_end) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Soft preferences: add penalties to avoid less desired meeting times.
# Walter's preferences:
#   - Avoid Monday (d == 0)
#   - Avoid Tuesday (d == 1)
#   - Avoid Thursday before 14:30 (d == 3 and s < 14:30 which is 14*60+30=870)
#   - Avoid Friday (d == 4)
# Grace's preferences:
#   - Avoid Wednesday (d == 2)

penalty = 0
penalty += If(d == 0, 1, 0)                      # Walter: Monday penalty
penalty += If(d == 1, 1, 0)                      # Walter: Tuesday penalty
penalty += If(And(d == 3, s < (14 * 60 + 30)), 1, 0)  # Walter: Thursday before 14:30 penalty
penalty += If(d == 4, 1, 0)                      # Walter: Friday penalty
penalty += If(d == 2, 1, 0)                      # Grace: Wednesday penalty

# Objective: first minimize the penalty, then minimize the meeting's time in the week.
opt.minimize(penalty)
opt.minimize(d * WORK_END + s)

# Check and print the result.
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