from z3 import Optimize, Int, If, Or, sat

# Meeting parameters
duration = 30  # half an hour meeting in minutes
WORK_START = 9 * 60    # 9:00 AM in minutes
WORK_END = 17 * 60     # 17:00 (5:00 PM) in minutes

# Map days: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Jeffrey's busy schedule (times in minutes)
# Monday: 11:30-12:00, 15:00-15:30
# Wednesday: 10:30-11:00, 13:30-14:00
# Thursday: 9:30-10:30
# Friday: 10:00-10:30, 11:00-11:30
jeffrey_busy = {
    0: [(11 * 60 + 30, 12 * 60), (15 * 60, 15 * 60 + 30)],
    2: [(10 * 60 + 30, 11 * 60), (13 * 60 + 30, 14 * 60)],
    3: [(9 * 60 + 30, 10 * 60 + 30)],
    4: [(10 * 60, 10 * 60 + 30), (11 * 60, 11 * 60 + 30)]
}
# Note: Jeffrey is free on Tuesday (day 1).

# Scott's busy schedule (times in minutes)
# Monday: 9:00-13:00, 13:30-17:00
# Tuesday: 9:30-11:00, 11:30-12:30, 13:00-13:30, 15:00-15:30, 16:00-16:30
# Wednesday: 9:00-17:00 (completely busy)
# Thursday: 9:00-12:30, 13:00-14:00, 14:30-17:00
# Friday: 9:00-9:30, 10:00-12:00, 13:00-14:00, 15:30-16:00, 16:30-17:00
scott_busy = {
    0: [(9 * 60, 13 * 60), (13 * 60 + 30, 17 * 60)],
    1: [(9 * 60 + 30, 11 * 60), (11 * 60 + 30, 12 * 60 + 30),
        (13 * 60, 13 * 60 + 30), (15 * 60, 15 * 60 + 30),
        (16 * 60, 16 * 60 + 30)],
    2: [(9 * 60, 17 * 60)],
    3: [(9 * 60, 12 * 60 + 30), (13 * 60, 14 * 60), (14 * 60 + 30, 17 * 60)],
    4: [(9 * 60, 9 * 60 + 30), (10 * 60, 12 * 60), (13 * 60, 14 * 60),
        (15 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)]
}

# Helper function: ensure that a meeting starting at 'start' with 'duration' doesn't overlap a busy interval.
def no_overlap(start, duration, busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Create the Z3 optimizer
opt = Optimize()

# Decision variables:
# d: day of the meeting index (0 to 4)
# s: meeting start time (minutes after midnight)
d = Int("d")
s = Int("s")

# Meeting must start and finish within working hours.
opt.add(s >= WORK_START, s + duration <= WORK_END)
opt.add(d >= 0, d <= 4)

# Constrain Jeffrey's schedule:
for day, intervals in jeffrey_busy.items():
    for (busy_start, busy_end) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Constrain Scott's schedule:
for day, intervals in scott_busy.items():
    for (busy_start, busy_end) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# We want the group to meet at their earliest availability.
# Use a lexicographic minimization of (day, start time).
opt.minimize(d * WORK_END + s)

# Check for a solution and print out the meeting time.
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