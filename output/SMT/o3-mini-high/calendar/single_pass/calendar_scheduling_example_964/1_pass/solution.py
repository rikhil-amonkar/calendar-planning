from z3 import *

# Define meeting duration in minutes
meeting_duration = 60

# We'll represent days as integers: 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday, 4 = Friday.
day = Int("day")
start = Int("start")  # Meeting start time in minutes from midnight.
end = start + meeting_duration

solver = Solver()

# The meeting must occur between 9:00 (540 minutes) and 17:00 (1020 minutes)
solver.add(day >= 0, day <= 4)
solver.add(start >= 540, end <= 1020)

# Betty cannot meet on Wednesday (2) and Thursday (3)
solver.add(day != 2, day != 3)

# Busy intervals are given per person as (day, busy_start, busy_end) where times are in minutes.
# Convert HH:MM to minutes (e.g., 10:00 -> 600)
# Busy times for Betty:
busy_betty = [
    # Monday (day 0)
    (0, 600, 630),   # 10:00 - 10:30
    (0, 690, 750),   # 11:30 - 12:30
    (0, 960, 990),   # 16:00 - 16:30
    # Tuesday (day 1)
    (1, 570, 600),   # 9:30 - 10:00
    (1, 630, 660),   # 10:30 - 11:00
    (1, 720, 750),   # 12:00 - 12:30
    (1, 810, 900),   # 13:30 - 15:00
    (1, 990, 1020),  # 16:30 - 17:00
    # Wednesday is not allowed for Betty so we don't need to add her busy slots here.
    # Friday (day 4)
    (4, 540, 600),   # 9:00 - 10:00
    (4, 690, 720),   # 11:30 - 12:00
    (4, 750, 780),   # 12:30 - 13:00
    (4, 870, 900)    # 14:30 - 15:00
]

# Busy times for Megan:
busy_megan = [
    # Monday (day 0)
    (0, 540, 1020),  # 9:00 - 17:00 (fully booked)
    # Tuesday (day 1)
    (1, 540, 570),   # 9:00 - 9:30
    (1, 600, 630),   # 10:00 - 10:30
    (1, 720, 840),   # 12:00 - 14:00
    (1, 900, 930),   # 15:00 - 15:30
    (1, 960, 990),   # 16:00 - 16:30
    # Wednesday (day 2)
    (2, 570, 630),   # 9:30 - 10:30
    (2, 660, 690),   # 11:00 - 11:30
    (2, 750, 780),   # 12:30 - 13:00
    (2, 810, 870),   # 13:30 - 14:30
    (2, 930, 1020),  # 15:30 - 17:00
    # Thursday (day 3)
    (3, 540, 630),   # 9:00 - 10:30
    (3, 690, 840),   # 11:30 - 14:00
    (3, 870, 900),   # 14:30 - 15:00
    (3, 930, 990),   # 15:30 - 16:30
    # Friday (day 4)
    (4, 540, 1020)   # 9:00 - 17:00 (fully booked)
]

# For each busy interval, if the meeting is on that day then the meeting must not overlap that interval.
def no_overlap(meeting_start, meeting_end, busy_start, busy_end):
    # The meeting must be completely before the busy interval or completely after.
    return Or(meeting_end <= busy_start, meeting_start >= busy_end)

for (d, busy_start, busy_end) in busy_betty:
    solver.add(Implies(day == d, no_overlap(start, end, busy_start, busy_end)))

for (d, busy_start, busy_end) in busy_megan:
    solver.add(Implies(day == d, no_overlap(start, end, busy_start, busy_end)))

# Check the constraints and extract a solution
if solver.check() == sat:
    model = solver.model()
    sol_day = model[day].as_long()
    sol_start = model[start].as_long()
    sol_end = sol_start + meeting_duration

    # Map day number back to day name
    day_names = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}

    # Function to convert minutes to HH:MM format (24-hour clock)
    def format_time(minutes):
        hour = minutes // 60
        minute = minutes % 60
        return f"{hour:02d}:{minute:02d}"

    print("SOLUTION:")
    print("Day:", day_names[sol_day])
    print("Start Time:", format_time(sol_start))
    print("End Time:", format_time(sol_end))
else:
    print("No solution found")