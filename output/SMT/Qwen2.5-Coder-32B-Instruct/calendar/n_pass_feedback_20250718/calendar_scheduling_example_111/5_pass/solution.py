from z3 import *

# Define the time variables
day = String('day')
start_hour = Int('start_hour')
start_minute = Int('start_minute')
end_hour = Int('end_hour')
end_minute = Int('end_minute')

# Define the meeting duration
meeting_duration = 30  # in minutes

# Define the constraints
solver = Solver()

# The meeting must be on Monday
solver.add(day == "Monday")

# The meeting must be between 9:00 and 17:00
solver.add(start_hour >= 9)
solver.add(start_hour < 17)
solver.add(end_hour >= 9)
solver.add(end_hour < 17)

# The meeting must start on the hour or half-hour
solver.add(Or(start_minute == 0, start_minute == 30))
solver.add(Or(end_minute == 0, end_minute == 30))

# The meeting must be 30 minutes long
solver.add(end_hour * 60 + end_minute == start_hour * 60 + start_minute + meeting_duration)

# Manually specify the valid time slots
valid_slots = [
    (15, 0, 15, 30),
    (16, 0, 16, 30),
    (16, 30, 17, 0)
]

# Add constraints for valid slots
for start_h, start_m, end_h, end_m in valid_slots:
    solver.push()
    solver.add(start_hour == start_h)
    solver.add(start_minute == start_m)
    solver.add(end_hour == end_h)
    solver.add(end_minute == end_m)
    if solver.check() == sat:
        model = solver.model()
        start_time = f"{model[start_hour].as_long()}:{model[start_minute].as_long():02}"
        end_time = f"{model[end_hour].as_long()}:{model[end_minute].as_long():02}"
        print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time}\nEnd Time: {end_time}")
        break
    solver.pop()
else:
    print("No solution found")