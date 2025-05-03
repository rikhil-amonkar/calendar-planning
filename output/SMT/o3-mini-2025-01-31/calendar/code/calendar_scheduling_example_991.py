from z3 import Optimize, Int, If, Or, sat

# Meeting parameters
duration = 30  # half an hour meeting in minutes
WORK_START = 9 * 60   # 9:00 AM in minutes (540)
WORK_END = 17 * 60    # 5:00 PM in minutes (1020)

# Map days: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Diana's busy schedule (times in minutes)
# Monday: 11:00-11:30, 12:00-12:30, 13:00-13:30, 14:30-15:30
# Tuesday: 10:30-11:30, 12:00-12:30, 15:00-15:30
# Wednesday: 9:30-10:00, 11:30-12:00, 12:30-15:30, 16:30-17:00
# Thursday: 9:00-9:30, 12:00-13:00, 14:00-16:30
# Friday: 9:30-10:00, 11:00-11:30, 12:00-13:30, 16:00-16:30
diana_busy = {
    0: [(11 * 60, 11 * 60 + 30), (12 * 60, 12 * 60 + 30),
        (13 * 60, 13 * 60 + 30), (14 * 60 + 30, 15 * 60 + 30)],
    1: [(10 * 60 + 30, 11 * 60 + 30), (12 * 60, 12 * 60 + 30),
        (15 * 60, 15 * 60 + 30)],
    2: [(9 * 60 + 30, 10 * 60), (11 * 60 + 30, 12 * 60),
        (12 * 60 + 30, 15 * 60 + 30), (16 * 60 + 30, 17 * 60)],
    3: [(9 * 60, 9 * 60 + 30), (12 * 60, 13 * 60),
        (14 * 60, 16 * 60 + 30)],
    4: [(9 * 60 + 30, 10 * 60), (11 * 60, 11 * 60 + 30),
        (12 * 60, 13 * 60 + 30), (16 * 60, 16 * 60 + 30)]
}

# Andrea's busy schedule (times in minutes)
# Monday: 9:00-12:30, 13:00-17:00
# Tuesday: 9:00-10:30, 11:30-16:00
# Wednesday: 9:00-12:30, 13:00-17:00
# Thursday: 9:00-11:00, 11:30-12:00, 12:30-13:30, 14:00-16:30
# Friday: 9:00-11:30, 12:00-14:00, 15:30-16:00
andrea_busy = {
    0: [(9 * 60, 12 * 60 + 30), (13 * 60, 17 * 60)],
    1: [(9 * 60, 10 * 60 + 30), (11 * 60 + 30, 16 * 60)],
    2: [(9 * 60, 12 * 60 + 30), (13 * 60, 17 * 60)],
    3: [(9 * 60, 11 * 60), (11 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60 + 30),
        (14 * 60, 16 * 60 + 30)],
    4: [(9 * 60, 11 * 60 + 30), (12 * 60, 14 * 60), (15 * 60 + 30, 16 * 60)]
}

# Helper function: Ensure that a meeting starting at 'start' with 'duration' minutes
# does not overlap a busy interval [busy_start, busy_end).
def no_overlap(start, duration, busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Create the Z3 optimizer
opt = Optimize()

# Decision variables:
# d : day of the meeting (integer: 0 for Monday, ..., 4 for Friday)
# s : meeting start time (in minutes after midnight)
d = Int("d")
s = Int("s")

# Enforce meeting to occur within working hours.
opt.add(s >= WORK_START, s + duration <= WORK_END)
opt.add(d >= 0, d <= 4)

# Add constraints for Diana's busy intervals.
for day, intervals in diana_busy.items():
    for (busy_start, busy_end) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Add constraints for Andrea's busy intervals.
for day, intervals in andrea_busy.items():
    for (busy_start, busy_end) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# The goal is to schedule the meeting as early as possible in the week.
# We minimize a combined expression that puts priority on earlier days and earlier times.
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