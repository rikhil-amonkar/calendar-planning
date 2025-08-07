from z3 import *

# Define the time variables
day = String('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the meeting duration
meeting_duration = 60  # 1 hour

# Define the constraints
solver = Solver()

# All meetings must be on Monday
solver.add(day == "Monday")

# Define the time constraints for each participant
# Anthony's busy times: 9:30 to 10:00, 12:00 to 13:00, 16:00 to 16:30
solver.add(Or(start_time + meeting_duration <= 570, start_time >= 600))  # 9:30 to 10:00
solver.add(Or(start_time + meeting_duration <= 720, start_time >= 780))  # 12:00 to 13:00
solver.add(Or(start_time + meeting_duration <= 960, start_time >= 990))  # 16:00 to 16:30

# Pamela's busy times: 9:30 to 10:00, 16:30 to 17:00
solver.add(Or(start_time + meeting_duration <= 570, start_time >= 600))  # 9:30 to 10:00
solver.add(Or(start_time + meeting_duration <= 990, start_time >= 1020))  # 16:30 to 17:00

# Zachary's busy times: 9:00 to 11:30, 12:00 to 12:30, 13:00 to 13:30, 14:30 to 15:00, 16:00 to 17:00
solver.add(Or(start_time + meeting_duration <= 540, start_time >= 690))  # 9:00 to 11:30
solver.add(Or(start_time + meeting_duration <= 720, start_time >= 750))  # 12:00 to 12:30
solver.add(Or(start_time + meeting_duration <= 780, start_time >= 810))  # 13:00 to 13:30
solver.add(Or(start_time + meeting_duration <= 870, start_time >= 900))  # 14:30 to 15:00
solver.add(Or(start_time + meeting_duration <= 960, start_time >= 1020))  # 16:00 to 17:00

# Pamela's preference: do not meet after 14:30
solver.add(start_time + meeting_duration <= 870)  # 14:30

# Meeting must be within work hours (9:00 to 17:00)
solver.add(start_time >= 540)  # 9:00
solver.add(start_time + meeting_duration <= 1020)  # 17:00

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    start_time_minutes = model[start_time].as_long()
    end_time_minutes = start_time_minutes + meeting_duration

    # Convert minutes to HH:MM format
    start_hour = start_time_minutes // 60
    start_minute = start_time_minutes % 60
    end_hour = end_time_minutes // 60
    end_minute = end_time_minutes % 60

    print(f"SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")