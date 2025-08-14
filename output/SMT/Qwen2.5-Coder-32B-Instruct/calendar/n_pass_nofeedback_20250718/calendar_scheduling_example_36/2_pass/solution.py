from z3 import *

# Define the time variables
day = Int('day')
start_hour = Int('start_hour')
start_minute = Int('start_minute')
end_hour = Int('end_hour')
end_minute = Int('end_minute')

# Define the constraints
solver = Solver()

# Meeting duration is 1 hour
solver.add(end_hour == start_hour + 1)
solver.add(end_minute == start_minute)

# Meeting should be between 9:00 and 17:00 on Monday
solver.add(day == 1)  # Monday is represented by 1
solver.add(start_hour >= 9)
solver.add(start_hour < 17)
solver.add(start_minute >= 0)
solver.add(start_minute < 60)

# Ryan's busy times: 9:00 to 9:30, 12:30 to 13:00
solver.add(Or(start_hour > 9, start_hour == 9 and start_minute >= 30))
solver.add(Or(end_hour < 12, end_hour == 12 and end_minute <= 30))

# Ruth is free all day, so no additional constraints for Ruth

# Denise's busy times: 9:30 to 10:30, 12:00 to 13:00, 14:30 to 16:30
# Denise does not want to meet after 12:30, which means the meeting must end by 12:30
solver.add(Or(start_hour > 10, start_hour == 10 and start_minute >= 30))
solver.add(Or(end_hour < 12, end_hour == 12 and end_minute <= 0))
solver.add(Or(start_hour > 13, start_hour == 13 and start_minute >= 0))
solver.add(Or(end_hour < 14, end_hour == 14 and end_minute <= 30))
solver.add(end_hour < 12)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_time = f"{model[start_hour].as_long()}:{model[start_minute].as_long():02}"
    end_time = f"{model[end_hour].as_long()}:{model[end_minute].as_long():02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")