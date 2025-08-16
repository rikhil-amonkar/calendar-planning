from z3 import *

# Create an optimizer
opt = Optimize()

# Define variables:
# d is the day index where 0 = Monday, 1 = Tuesday, 2 = Wednesday.
# start is the meeting start time in minutes from midnight.
d = Int('d')
start = Int('start')
meeting_duration = 30
end = start + meeting_duration

# Working hours: meetings can only start from 9:00 (540 minutes) until 16:30 (990 minutes)
opt.add(Or(d == 0, d == 1, d == 2))
opt.add(start >= 540, start <= 1020 - meeting_duration)

# Busy intervals (in minutes since midnight)
# Each tuple is (day, busy_start, busy_end)
# Nancy's busy times:
# Monday: 10:00-10:30, 11:30-12:30, 13:30-14:00, 14:30-15:30, 16:00-17:00
# Tuesday: 9:30-10:30, 11:00-11:30, 12:00-12:30, 13:00-13:30, 15:30-16:00
# Wednesday: 10:00-11:30, 13:30-16:00
# Jose's busy times:
# Monday: 9:00-17:00, Tuesday: 9:00-17:00,
# Wednesday: 9:00-9:30, 10:00-12:30, 13:30-14:30, 15:00-17:00
busy_intervals = [
    # Nancy's scheduled blocks
    (0, 600, 630),   # Monday 10:00 to 10:30
    (0, 690, 750),   # Monday 11:30 to 12:30
    (0, 810, 840),   # Monday 13:30 to 14:00
    (0, 870, 930),   # Monday 14:30 to 15:30
    (0, 960, 1020),  # Monday 16:00 to 17:00

    (1, 570, 630),   # Tuesday 9:30 to 10:30
    (1, 660, 690),   # Tuesday 11:00 to 11:30
    (1, 720, 750),   # Tuesday 12:00 to 12:30
    (1, 780, 810),   # Tuesday 13:00 to 13:30
    (1, 930, 960),   # Tuesday 15:30 to 16:00

    (2, 600, 690),   # Wednesday 10:00 to 11:30
    (2, 810, 960),   # Wednesday 13:30 to 16:00

    # Jose's scheduled blocks
    (0, 540, 1020),  # Monday 9:00 to 17:00
    (1, 540, 1020),  # Tuesday 9:00 to 17:00

    (2, 540, 570),   # Wednesday 9:00 to 9:30
    (2, 600, 750),   # Wednesday 10:00 to 12:30
    (2, 810, 870),   # Wednesday 13:30 to 14:30
    (2, 900, 1020)   # Wednesday 15:00 to 17:00
]

# For each busy interval, if the meeting is scheduled on that day,
# then the meeting must not overlap with the busy interval.
for (busy_day, busy_start, busy_end) in busy_intervals:
    # Non-overlap condition: meeting ends before a busy slot starts or starts after it ends.
    opt.add(Implies(d == busy_day, Or(end <= busy_start, start >= busy_end)))

# To find the earliest available slot, we minimize the “combined time”
# where combined = d * 1440 + start.
# (This way, earlier days and times get a lower score.)
combined = d * 1440 + start
opt.minimize(combined)

# Check for a solution and, if found, produce the meeting time.
if opt.check() == sat:
    model = opt.model()
    chosen_day = model[d].as_long()
    chosen_start = model[start].as_long()
    chosen_end = chosen_start + meeting_duration

    # Format the meeting time in HH:MM (24-hour format)
    def format_time(t):
        hours = t // 60
        minutes = t % 60
        return f"{hours:02d}:{minutes:02d}"

    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday"}
    output = "SOLUTION:\n"
    output += f"Day: {day_names[chosen_day]}\n"
    output += f"Start Time: {format_time(chosen_start)}\n"
    output += f"End Time: {format_time(chosen_end)}"
    print(output)
else:
    print("No solution found.")