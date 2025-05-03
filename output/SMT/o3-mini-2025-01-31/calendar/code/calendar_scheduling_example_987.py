from z3 import Optimize, Int, If, Or, sat

# Meeting parameters
duration = 30  # meeting duration in minutes
WORK_START = 9 * 60   # 9:00 in minutes (540)
WORK_END = 17 * 60    # 17:00 in minutes (1020)

# Map days: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Shirley's busy schedule (in minutes)
# Tuesday: 9:30-10:30, 16:00-16:30
# Wednesday: 14:30-15:00
# Thursday: 9:30-10:00
# Friday: 11:30-12:00
shirley_busy = {
    1: [(9 * 60 + 30, 10 * 60 + 30), (16 * 60, 16 * 60 + 30)],
    2: [(14 * 60 + 30, 15 * 60)],
    3: [(9 * 60 + 30, 10 * 60)],
    4: [(11 * 60 + 30, 12 * 60)]
}

# Tyler's busy schedule (in minutes)
# Monday: 9:30-11:30, 13:00-13:30, 14:00-16:00, 16:30-17:00
# Tuesday: 9:00-9:30, 10:00-12:00, 12:30-13:00, 13:30-14:30, 16:00-17:00
# Wednesday: 9:00-9:30, 10:30-11:00, 12:00-12:30, 14:00-15:30, 16:00-16:30
# Thursday: 9:00-13:30, 14:00-17:00
# Friday: 9:00-17:00
tyler_busy = {
    0: [(9 * 60 + 30, 11 * 60 + 30), (13 * 60, 13 * 60 + 30),
        (14 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)],
    1: [(9 * 60, 9 * 60 + 30), (10 * 60, 12 * 60), (12 * 60 + 30, 13 * 60),
        (13 * 60 + 30, 14 * 60 + 30), (16 * 60, 17 * 60)],
    2: [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 11 * 60), (12 * 60, 12 * 60 + 30),
        (14 * 60, 15 * 60 + 30), (16 * 60, 16 * 60 + 30)],
    3: [(9 * 60, 13 * 60 + 30), (14 * 60, 17 * 60)],
    4: [(9 * 60, 17 * 60)]
}

# Helper function: meeting starting at 'start' with 'duration' minutes does not overlap a busy interval.
def no_overlap(start, duration, busy_start, busy_end):
    # Meeting ends before busy interval or starts after busy interval
    return Or(start + duration <= busy_start, start >= busy_end)

# Create the Z3 optimizer
opt = Optimize()

# Decision variables:
# d: day of the meeting (0=Monday, ..., 4=Friday)
# s: meeting start time in minutes after midnight
d = Int("d")
s = Int("s")

# Meeting must be within work hours
opt.add(s >= WORK_START, s + duration <= WORK_END)
opt.add(d >= 0, d <= 4)

# Add Shirley's busy constraints
for day, intervals in shirley_busy.items():
    for (busy_start, busy_end) in intervals:
        # If meeting is scheduled on 'day', ensure no overlap with busy interval.
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Add Tyler's busy constraints
for day, intervals in tyler_busy.items():
    for (busy_start, busy_end) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Soft preference: Shirley would rather not meet on Monday (day 0)
preference_penalty = If(d == 0, 1, 0)
opt.minimize(preference_penalty)

# Additionally, we want the meeting at the earliest availability.
# We minimize a combined measure that represents day and time.
opt.minimize(d * WORK_END + s)

# Find and print the solution.
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