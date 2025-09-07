from z3 import *

# Meeting duration in minutes
duration = 30

# Define variables:
# t is the starting time in minutes from midnight.
# d is the day, where 0 = Monday, 1 = Tuesday, 2 = Wednesday.
t = Int('t')
d = Int('d')

opt = Optimize()

# Working hours: meeting must start between 9:00 (540 minutes) and 16:30 (990 minutes)
opt.add(t >= 540, t <= 990)
opt.add(Or(d == 0, d == 1, d == 2))

# Define busy intervals (in minutes) for Samuel.
# Note: Larry's calendar is completely free, but he prefers not to meet on Wednesday.
#
# Monday busy intervals:
#   10:30 to 11:00  -> [630, 660)
#   12:00 to 12:30  -> [720, 750)
#   13:00 to 15:00  -> [780, 900)
#   15:30 to 16:30  -> [930, 990)
monday_busy = [(630, 660), (720, 750), (780, 900), (930, 990)]
for start_busy, end_busy in monday_busy:
    # If meeting is on Monday, then it must not overlap any busy interval.
    opt.add(Implies(d == 0, Or(t + duration <= start_busy, t >= end_busy)))

# Tuesday busy intervals:
#   9:00 to 12:00   -> [540, 720)
#   14:00 to 15:30  -> [840, 930)
#   16:30 to 17:00  -> [990, 1020)
tuesday_busy = [(540, 720), (840, 930), (990, 1020)]
for start_busy, end_busy in tuesday_busy:
    opt.add(Implies(d == 1, Or(t + duration <= start_busy, t >= end_busy)))

# Wednesday busy intervals:
#   10:30 to 11:00  -> [630, 660)
#   11:30 to 12:00  -> [690, 720)
#   12:30 to 13:00  -> [750, 780)
#   14:00 to 14:30  -> [840, 870)
#   15:00 to 16:00  -> [900, 960)
wednesday_busy = [(630, 660), (690, 720), (750, 780), (840, 870), (900, 960)]
for start_busy, end_busy in wednesday_busy:
    opt.add(Implies(d == 2, Or(t + duration <= start_busy, t >= end_busy)))

# Preferences:
# - Larry would rather not meet on Wednesday.
# - Samuel would like to avoid more meetings on Tuesday.
# - The group wants to meet at their earliest availability.
#
# We encode these as a cost function and minimize it.
# We assign:
#   Monday: no penalty (cost = t)
#   Tuesday: add a penalty (cost = t + 10000)
#   Wednesday: add a larger penalty (cost = t + 20000)
cost = If(d == 0, t, If(d == 1, t + 10000, t + 20000))
opt.minimize(cost)

# Check for a solution and output the meeting time and day in the required format.
if opt.check() == sat:
    model = opt.model()
    meeting_day = model[d].as_long()
    meeting_start = model[t].as_long()
    meeting_end = meeting_start + duration

    # Helper function to format minutes as HH:MM
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    time_range = f"{format_time(meeting_start)}-{format_time(meeting_end)}"
    days = ["Monday", "Tuesday", "Wednesday"]
    day_str = days[meeting_day]

    print(time_range)
    print(day_str)
else:
    print("No solution found.")