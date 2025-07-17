from z3 import *

# Define the time variables
day = Int('day')
start_hour = Int('start_hour')
start_minute = Int('start_minute')
end_hour = Int('end_hour')
end_minute = Int('end_minute')

# Define the constraints
solver = Solver()

# Meeting duration is 30 minutes
solver.add(end_hour * 60 + end_minute == start_hour * 60 + start_minute + 30)

# Meeting should be between 9:00 and 17:00 on Monday
solver.add(day == 1)  # Monday
solver.add(start_hour >= 9)
solver.add(start_hour < 17)
solver.add(start_minute >= 0)
solver.add(start_minute < 60)
solver.add(end_hour >= 9)
solver.add(end_hour < 17)
solver.add(end_minute >= 0)
solver.add(end_minute < 60)

# Judy is free the entire day, so no additional constraints for her

# Nicole's busy times: 9:00 to 10:00, 10:30 to 16:30
# Nicole would rather not meet before 16:00, so we add a preference for times after 16:00
solver.add(Or(
    Or(start_hour * 60 + start_minute >= 10 * 60, start_hour * 60 + start_minute < 9 * 60),
    Or(start_hour * 60 + start_minute >= 16 * 60 + 30, start_hour * 60 + start_minute < 10 * 60 + 30)
))

# Ensure the meeting does not overlap with Nicole's busy times
solver.add(Or(
    start_hour * 60 + start_minute >= 10 * 60,  # After 10:00
    end_hour * 60 + end_minute <= 10 * 60      # Before 10:00
))
solver.add(Or(
    start_hour * 60 + start_minute >= 16 * 60 + 30,  # After 16:30
    end_hour * 60 + end_minute <= 10 * 60 + 30       # Before 10:30
))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    start_time = model[start_hour].as_long(), model[start_minute].as_long()
    end_time = model[end_hour].as_long(), model[end_minute].as_long()
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time[0]:02}:{start_time[1]:02}\nEnd Time: {end_time[0]:02}:{end_time[1]:02}")
else:
    print("No solution found")