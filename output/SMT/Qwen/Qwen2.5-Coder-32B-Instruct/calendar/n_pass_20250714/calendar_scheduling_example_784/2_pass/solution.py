from z3 import *

# Define the variables
day = Int('day')  # 1 for Monday, 2 for Tuesday, 3 for Wednesday
start_time = Int('start_time')  # in minutes since 9:00

# Define the constraints
constraints = []

# Meeting duration is 1 hour (60 minutes)
meeting_duration = 60

# Define the available time slots for each day
available_times = {
    1: [(0, 540), (60, 720)],  # Monday: 9:00-9:30 and 10:30-12:30
    2: [(60, 810)],            # Tuesday: 10:30-13:30
    3: [(720, 960)]            # Wednesday: 12:00-16:00
}

# Add constraints for available times
for d, times in available_times.items():
    constraints.append(Or([And(start_time >= s, start_time + meeting_duration <= e) for s, e in times]))

# Add constraint for the day
constraints.append(Or(day == 1, day == 2, day == 3))

# Judith prefers not to have meetings on Monday
constraints.append(day != 1)

# Judith prefers not to have meetings before 12:00 on Wednesday
constraints.append(Or(day != 3, start_time >= 180))  # 180 minutes is 12:00

# Create the solver and add constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start_time = model[start_time].as_long()

    # Convert the start time from minutes since 9:00 to HH:MM format
    start_hour = 9 + meeting_start_time // 60
    start_minute = meeting_start_time % 60
    end_hour = start_hour + meeting_duration // 60
    end_minute = start_minute + meeting_duration % 60

    # Format the output
    day_name = {1: "Monday", 2: "Tuesday", 3: "Wednesday"}[meeting_day]
    start_time_str = f"{start_hour:02}:{start_minute:02}"
    end_time_str = f"{end_hour:02}:{end_minute:02}"

    print(f"SOLUTION:\nDay: {day_name}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")