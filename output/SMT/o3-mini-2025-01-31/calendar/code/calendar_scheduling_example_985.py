from z3 import Optimize, Int, If, Or, sat

# Meeting parameters
duration = 60  # meeting duration in minutes (1 hour)
WORK_START = 9 * 60   # 9:00 in minutes (540)
WORK_END = 17 * 60    # 17:00 in minutes (1020)

# Map days (0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday)
day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

# Diane's busy schedule (in minutes)
# Monday: 12:00-12:30, 15:00-15:30
# Tuesday: 10:00-11:00, 11:30-12:00, 12:30-13:00, 16:00-17:00
# Wednesday: 9:00-9:30, 14:30-15:00, 16:30-17:00
# Thursday: 15:30-16:30
# Friday: 9:30-11:30, 14:30-15:00, 16:00-17:00
diane_busy = {
    0: [(12 * 60, 12 * 60 + 30), (15 * 60, 15 * 60 + 30)],
    1: [(10 * 60, 11 * 60), (11 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60), (16 * 60, 17 * 60)],
    2: [(9 * 60, 9 * 60 + 30), (14 * 60 + 30, 15 * 60), (16 * 60 + 30, 17 * 60)],
    3: [(15 * 60 + 30, 16 * 60 + 30)],
    4: [(9 * 60 + 30, 11 * 60 + 30), (14 * 60 + 30, 15 * 60), (16 * 60, 17 * 60)]
}

# Matthew's busy schedule (in minutes)
# Monday: 9:00-10:00, 10:30-17:00
# Tuesday: 9:00-17:00
# Wednesday: 9:00-11:00, 12:00-14:30, 16:00-17:00
# Thursday: 9:00-16:00
# Friday: 9:00-17:00
matthew_busy = {
    0: [(9 * 60, 10 * 60), (10 * 60 + 30, 17 * 60)],
    1: [(9 * 60, 17 * 60)],
    2: [(9 * 60, 11 * 60), (12 * 60, 14 * 60 + 30), (16 * 60, 17 * 60)],
    3: [(9 * 60, 16 * 60)],
    4: [(9 * 60, 17 * 60)]
}

# Helper function: the meeting starting at 'start' with 'duration' minutes 
# does not overlap with a busy interval from busy_start to busy_end.
def no_overlap(start, duration, busy_start, busy_end):
    return Or(start + duration <= busy_start, start >= busy_end)

# Create the Z3 optimizer
opt = Optimize()

# Decision variables:
# d: day of meeting (0 to 4),
# s: meeting start time (in minutes after midnight)
d = Int("d")
s = Int("s")

# The meeting must be within work hours
opt.add(s >= WORK_START, s + duration <= WORK_END)
opt.add(d >= 0, d <= 4)

# Add constraints for Diane's busy schedule.
for day, intervals in diane_busy.items():
    for (busy_start, busy_end) in intervals:
        # If the meeting is scheduled on day, it must not overlap with any busy intervals.
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Add constraints for Matthew's busy schedule.
for day, intervals in matthew_busy.items():
    for (busy_start, busy_end) in intervals:
        opt.add(If(d == day, no_overlap(s, duration, busy_start, busy_end), True))

# Matthew's preference: he would rather not meet on Wednesday before 12:30.
# We'll add a soft penalty for scheduling on Wednesday (d==2) with a start time before 12:30 (750 minutes).
matthew_penalty = If((d == 2) and (s < 12 * 60 + 30), 1, 0)
opt.minimize(matthew_penalty)

# Additionally, we can prefer an earlier meeting by minimizing a combined expression
# that factors both the day and start time.
opt.minimize(d * WORK_END + s)

# Solve and print the meeting time.
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