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

# Gregory's availability
solver.add(Or(start_hour * 60 + start_minute >= 10 * 60,
              start_hour * 60 + start_minute < 9 * 60,
              And(start_hour * 60 + start_minute >= 11 * 60 + 30,
                  start_hour * 60 + start_minute < 12 * 60 + 30),
              And(start_hour * 60 + start_minute >= 13 * 60 + 30,
                  start_hour * 60 + start_minute < 14 * 60),
              And(start_hour * 60 + start_minute >= 14 * 60 + 30,
                  start_hour * 60 + start_minute < 15 * 60)))

# Christine's availability
solver.add(Or(start_hour * 60 + start_minute >= 11 * 60 + 30,
              start_hour * 60 + start_minute < 9 * 60,
              And(start_hour * 60 + start_minute >= 13 * 60 + 30,
                  start_hour * 60 + start_minute < 17 * 60)))

# Vincent's availability
solver.add(Or(start_hour * 60 + start_minute >= 9 * 60 + 30,
              start_hour * 60 + start_minute < 9 * 60,
              And(start_hour * 60 + start_minute >= 12 * 60,
                  start_hour * 60 + start_minute < 10 * 60 + 30),
              And(start_hour * 60 + start_minute >= 14 * 60,
                  start_hour * 60 + start_minute < 12 * 60 + 30),
              And(start_hour * 60 + start_minute >= 17 * 60,
                  start_hour * 60 + start_minute < 14 * 60 + 30)))

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    start_time = f"{model[start_hour].as_long()}:{model[start_minute].as_long():02}"
    end_time = f"{model[end_hour].as_long()}:{model[end_minute].as_long():02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")