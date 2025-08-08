from z3 import *

# Define the days of the week
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

# Create a Z3 optimizer
opt = Optimize()

# Define the meeting day and time
meeting_day = Int('meeting_day')
meeting_start_hour = Int('meeting_start_hour')
meeting_start_minute = Int('meeting_start_minute')

# Constraints for the meeting day
opt.add(meeting_day >= 0)
opt.add(meeting_day < len(days))

# Constraints for the meeting start time
opt.add(meeting_start_hour >= 9)
opt.add(meeting_start_hour < 17)
opt.add(Or(meeting_start_minute == 0, meeting_start_minute == 30))

# Define the meeting duration (1 hour)
meeting_end_hour = meeting_start_hour + 1
meeting_end_minute = meeting_start_minute

# Brian's busy times
brian_busy_times = [
    ("Monday", 9, 30, 10, 0),
    ("Monday", 12, 30, 14, 30),
    ("Monday", 15, 30, 16, 0),
    ("Tuesday", 9, 0, 9, 30),
    ("Wednesday", 12, 30, 14, 0),
    ("Wednesday", 16, 30, 17, 0),
    ("Thursday", 11, 0, 11, 30),
    ("Thursday", 13, 0, 13, 30),
    ("Thursday", 16, 30, 17, 0),
    ("Friday", 9, 30, 10, 0),
    ("Friday", 10, 30, 11, 0),
    ("Friday", 13, 0, 13, 30),
    ("Friday", 15, 0, 16, 0),
    ("Friday", 16, 30, 17, 0),
]

# Julia's busy times
julia_busy_times = [
    ("Monday", 9, 0, 10, 0),
    ("Monday", 11, 0, 11, 30),
    ("Monday", 12, 30, 13, 0),
    ("Monday", 15, 30, 16, 0),
    ("Tuesday", 13, 0, 14, 0),
    ("Tuesday", 16, 0, 16, 30),
    ("Wednesday", 9, 0, 11, 30),
    ("Wednesday", 12, 0, 12, 30),
    ("Wednesday", 13, 0, 17, 0),
    ("Thursday", 9, 0, 10, 30),
    ("Thursday", 11, 0, 17, 0),
    ("Friday", 9, 0, 10, 0),
    ("Friday", 10, 30, 11, 30),
    ("Friday", 12, 30, 14, 0),
    ("Friday", 14, 30, 15, 0),
    ("Friday", 15, 30, 16, 0),
]

# Add constraints to avoid busy times
for day, start_h, start_m, end_h, end_m in brian_busy_times:
    opt.add(Or(meeting_day != days.index(day),
              meeting_start_hour > end_h,
              meeting_start_hour == end_h and meeting_start_minute >= end_m,
              meeting_end_hour < start_h,
              meeting_end_hour == start_h and meeting_end_minute <= start_m))

for day, start_h, start_m, end_h, end_m in julia_busy_times:
    opt.add(Or(meeting_day != days.index(day),
              meeting_start_hour > end_h,
              meeting_start_hour == end_h and meeting_start_minute >= end_m,
              meeting_end_hour < start_h,
              meeting_end_hour == start_h and meeting_end_minute <= start_m))

# Preference: Avoid Monday if possible
opt.minimize(If(meeting_day == 0, 1, 0))

# Solve the problem
if opt.check() == sat:
    model = opt.model()
    day_index = model[meeting_day].as_long()
    start_h = model[meeting_start_hour].as_long()
    start_m = model[meeting_start_minute].as_long()
    end_h = start_h + 1
    end_m = start_m

    # Format the output
    start_time = f"{start_h:02}:{start_m:02}"
    end_time = f"{end_h:02}:{end_m:02}"
    print(f"SOLUTION:\nDay: {days[day_index]}\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")