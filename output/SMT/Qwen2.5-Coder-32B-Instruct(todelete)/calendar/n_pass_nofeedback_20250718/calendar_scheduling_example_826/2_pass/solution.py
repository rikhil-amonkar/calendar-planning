from z3 import *

# Define the days of the week
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

# Define the time slots in 30-minute increments from 9:00 to 17:00
time_slots = [(h, m) for h in range(9, 17) for m in [0, 30]]

# Create a Z3 solver instance
solver = Solver()

# Define variables for the day, hour, and minute
day_var = Int('day')
hour_var = Int('hour')
minute_var = Int('minute')

# Constraints for the day
solver.add(day_var >= 0)
solver.add(day_var < len(days))

# Constraints for the time slot
solver.add(hour_var >= 9)
solver.add(hour_var < 17)
solver.add(Or(minute_var == 0, minute_var == 30))

# Cheryl's schedule is always open, so no additional constraints for her

# James's schedule constraints
james_busy_times = {
    "Monday": [(9, 0, 9, 30), (10, 30, 11, 0), (12, 30, 13, 0), (14, 30, 15, 30), (16, 30, 17, 0)],
    "Tuesday": [(9, 0, 11, 0), (11, 30, 12, 0), (12, 30, 15, 30), (16, 0, 17, 0)],
    "Wednesday": [(10, 0, 11, 0), (12, 0, 13, 0), (13, 30, 16, 0)],
    "Thursday": [(9, 30, 11, 30), (12, 0, 12, 30), (13, 0, 13, 30), (14, 0, 14, 30), (16, 30, 17, 0)]
}

# Add constraints to avoid James's busy times
for day, busy_times in james_busy_times.items():
    day_index = days.index(day)
    for start_h, start_m, end_h, end_m in busy_times:
        # Convert times to 30-minute slots
        start_slot = start_h * 2 + (start_m // 30)
        end_slot = end_h * 2 + (end_m // 30)
        # Add constraints to avoid these slots
        time_slot = hour_var * 2 + If(minute_var == 30, 1, 0)
        solver.add(Or(day_var != day_index, Or(time_slot < start_slot, time_slot >= end_slot)))

# Cheryl's preference not to meet on Wednesday or Thursday
solver.add(day_var != days.index("Wednesday"))
solver.add(day_var != days.index("Thursday"))

# Define the meeting duration (30 minutes)
meeting_duration = 1  # in 30-minute slots

# Ensure the meeting fits within the day
solver.add(hour_var * 2 + If(minute_var == 30, 1, 0) + meeting_duration <= 16 * 2)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    day_index = model[day_var].as_long()
    hour = model[hour_var].as_long()
    minute = model[minute_var].as_long()
    end_hour = hour + (minute + 30) // 60
    end_minute = (minute + 30) % 60
    print(f"SOLUTION:\nDay: {days[day_index]}\nStart Time: {hour:02}:{minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")