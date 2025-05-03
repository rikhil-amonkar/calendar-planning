from z3 import Optimize, Int, If, Or, sat

# Meeting parameters
duration = 30  # duration in minutes
WORK_START = 9 * 60   # work day starts at 9:00 AM (540 minutes)
WORK_END = 17 * 60    # work day ends at 17:00 (1020 minutes)

# Map days: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Henry is free all week, so no busy intervals for Henry.

# Amanda's busy schedule in minutes:
# Monday: 9:00-10:00, 10:30-12:30, 13:00-17:00
# Tuesday: 9:30-10:00, 12:30-16:30
# Wednesday: 9:00-10:30, 11:00-11:30, 12:00-13:00, 13:30-16:30
# Thursday: 9:30-11:30, 12:00-14:30, 16:30-17:00
# Friday: 10:00-11:00, 11:30-12:30, 13:00-13:30, 14:30-15:30
amanda_busy = {
    0: [(9 * 60, 10 * 60), (10 * 60 + 30, 12 * 60 + 30), (13 * 60, 17 * 60)],
    1: [(9 * 60 + 30, 10 * 60), (12 * 60 + 30, 16 * 60 + 30)],
    2: [(9 * 60, 10 * 60 + 30), (11 * 60, 11 * 60 + 30),
        (12 * 60, 13 * 60), (13 * 60 + 30, 16 * 60 + 30)],
    3: [(9 * 60 + 30, 11 * 60 + 30), (12 * 60, 14 * 60 + 30),
        (16 * 60 + 30, 17 * 60)],
    4: [(10 * 60, 11 * 60), (11 * 60 + 30, 12 * 60 + 30),
        (13 * 60, 13 * 60 + 30), (14 * 60 + 30, 15 * 60 + 30)]
}

# Helper function to ensure that a meeting starting at 'start' with given 'duration'
# does not overlap a busy interval from 'busy_start' to 'busy_end'.
def no_overlap(start, duration, busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Create the Z3 optimizer
opt = Optimize()

# Decision variables:
# d: day of the meeting (0 for Monday to 4 for Friday)
# s: meeting start time in minutes (within that day)
d = Int("d")
s = Int("s")

# Constraint: meeting must be scheduled within work hours.
opt.add(s >= WORK_START, s + duration <= WORK_END)
opt.add(d >= 0, d <= 4)

# Add Amanda's busy constraints: if the meeting is on a day Amanda is busy during an interval,
# then the meeting must not overlap that busy interval.
for day, intervals in amanda_busy.items():
    for busy_start, busy_end in intervals:
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# The group prefers meeting at their earliest availability.
# We'll prioritize the earliest day and then the earliest time in the day.
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