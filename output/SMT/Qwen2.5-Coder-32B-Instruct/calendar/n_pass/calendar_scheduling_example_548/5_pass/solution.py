from z3 import *

# Define the time variables
day = Int('day')
start_hour = Int('start_hour')
start_minute = Int('start_minute')
end_hour = Int('end_hour')
end_minute = Int('end_minute')

# Create an optimizer
optimizer = Optimize()

# Meeting duration is 30 minutes
optimizer.add(end_hour * 60 + end_minute == start_hour * 60 + start_minute + 30)

# Meeting should be between 9:00 and 17:00 on Monday
optimizer.add(day == 1)  # Monday
optimizer.add(start_hour * 60 + start_minute >= 9 * 60)
optimizer.add(end_hour * 60 + end_minute <= 17 * 60)

# Judy is free the entire day, so no additional constraints for her

# Nicole's busy times: 9:00 to 10:00, 10:30 to 16:30
# Ensure the meeting does not overlap with Nicole's busy times
optimizer.add(Or(
    start_hour * 60 + start_minute >= 10 * 60,  # After 10:00
    end_hour * 60 + end_minute <= 10 * 60 + 30  # Before 10:30
))
optimizer.add(Or(
    start_hour * 60 + start_minute >= 16 * 60 + 30,  # After 16:30
    end_hour * 60 + end_minute <= 10 * 60 + 30  # Before 10:30
))

# Prefer times after 16:00 for Nicole
optimizer.minimize(If(start_hour * 60 + start_minute < 16 * 60, 16 * 60 - (start_hour * 60 + start_minute), 0))

# Ensure that start and end times are valid
optimizer.add(start_hour >= 9)
optimizer.add(start_hour < 17)
optimizer.add(end_hour >= 9)
optimizer.add(end_hour < 17)
optimizer.add(start_minute >= 0)
optimizer.add(start_minute < 60)
optimizer.add(end_minute >= 0)
optimizer.add(end_minute < 60)

# Solve the problem
if optimizer.check() == sat:
    model = optimizer.model()
    start_time = model[start_hour].as_long(), model[start_minute].as_long()
    end_time = model[end_hour].as_long(), model[end_minute].as_long()
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time[0]:02}:{start_time[1]:02}\nEnd Time: {end_time[0]:02}:{end_time[1]:02}")
else:
    print("No solution found")