from z3 import Optimize, Int, Implies, Or, If, sat

# Create an Optimize object
opt = Optimize()

# Define the meeting variables:
# day: 0=Monday, 1=Tuesday, 2=Wednesday, 3=Thursday, 4=Friday
day = Int("day")
meeting_start = Int("meeting_start")  # meeting start time in minutes since midnight
duration = 30
meeting_end = meeting_start + duration

# Work hours: between 09:00 (540 minutes) and 17:00 (1020 minutes)
# Meeting must finish by 17:00, so meeting_start <= 1020 - 30 = 990 minutes.
opt.add(day >= 0, day <= 4)
opt.add(meeting_start >= 540, meeting_start <= 990)

# Define busy intervals (in minutes) for each participant 
# Format: (day, busy_start, busy_end)
# Days: 0-Monday, 1-Tuesday, 2-Wednesday, 3-Thursday, 4-Friday

busy_intervals = [
    # Terry's busy intervals
    (0, 630, 660),   # Monday: 10:30-11:00
    (0, 750, 840),   # Monday: 12:30-14:00
    (0, 900, 1020),  # Monday: 15:00-17:00
    (1, 570, 600),   # Tuesday: 9:30-10:00
    (1, 630, 660),   # Tuesday: 10:30-11:00
    (1, 840, 870),   # Tuesday: 14:00-14:30
    (1, 960, 990),   # Tuesday: 16:00-16:30
    (2, 570, 630),   # Wednesday: 9:30-10:30
    (2, 660, 720),   # Wednesday: 11:00-12:00
    (2, 780, 810),   # Wednesday: 13:00-13:30
    (2, 900, 960),   # Wednesday: 15:00-16:00
    (2, 990, 1020),  # Wednesday: 16:30-17:00
    (3, 570, 600),   # Thursday: 9:30-10:00
    (3, 720, 750),   # Thursday: 12:00-12:30
    (3, 780, 870),   # Thursday: 13:00-14:30
    (3, 960, 990),   # Thursday: 16:00-16:30
    (4, 540, 690),   # Friday: 9:00-11:30
    (4, 720, 750),   # Friday: 12:00-12:30
    (4, 810, 960),   # Friday: 13:30-16:00
    (4, 990, 1020),  # Friday: 16:30-17:00

    # Frances's busy intervals
    (0, 570, 660),   # Monday: 9:30-11:00
    (0, 690, 780),   # Monday: 11:30-13:00
    (0, 840, 870),   # Monday: 14:00-14:30
    (0, 900, 960),   # Monday: 15:00-16:00
    (1, 540, 570),   # Tuesday: 9:00-9:30
    (1, 600, 630),   # Tuesday: 10:00-10:30
    (1, 660, 720),   # Tuesday: 11:00-12:00
    (1, 780, 870),   # Tuesday: 13:00-14:30
    (1, 930, 990),   # Tuesday: 15:30-16:30
    (2, 570, 600),   # Wednesday: 9:30-10:00
    (2, 630, 660),   # Wednesday: 10:30-11:00
    (2, 690, 960),   # Wednesday: 11:30-16:00
    (2, 990, 1020),  # Wednesday: 16:30-17:00
    (3, 660, 750),   # Thursday: 11:00-12:30
    (3, 870, 1020),  # Thursday: 14:30-17:00
    (4, 570, 630),   # Friday: 9:30-10:30
    (4, 660, 750),   # Friday: 11:00-12:30
    (4, 780, 960),   # Friday: 13:00-16:00
    (4, 990, 1020)   # Friday: 16:30-17:00
]

# For each busy interval, if the meeting is scheduled on that day, the meeting must not overlap the busy time.
for (busy_day, busy_start, busy_end) in busy_intervals:
    opt.add(Implies(day == busy_day, Or(meeting_end <= busy_start, meeting_start >= busy_end)))

# Frances prefers to avoid additional meetings on Tuesday.
# We add a penalty if the meeting is scheduled on Tuesday.
penalty = If(day == 1, 100000, 0)

# We want the earliest available meeting:
# - First, avoid Tuesday (high penalty if day==1),
# - Then, choose the earliest day (lowest day value),
# - Then, choose the earliest start time.
cost = penalty + day * 10000 + meeting_start
opt.minimize(cost)

# Find and extract the optimal model
if opt.check() == sat:
    m = opt.model()
    selected_day = m[day].as_long()
    start = m[meeting_start].as_long()
    end = start + duration

    # Helper function to convert minutes to "HH:MM" format
    def format_time(total_minutes):
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    day_mapping = {0: "Monday", 1: "Tuesday", 2: "Wednesday", 3: "Thursday", 4: "Friday"}
    
    # Print the solution in the required format
    print("SOLUTION:")
    print("Day:", day_mapping[selected_day])
    print("Start Time:", format_time(start))
    print("End Time:", format_time(end))
else:
    print("No solution found.")