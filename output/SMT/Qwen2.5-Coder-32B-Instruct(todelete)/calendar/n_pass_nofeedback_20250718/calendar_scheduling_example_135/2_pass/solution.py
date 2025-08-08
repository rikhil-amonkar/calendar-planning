from z3 import *

# Define the time variables
day = Int('day')
start_hour = Int('start_hour')
start_minute = Int('start_minute')
end_hour = Int('end_hour')
end_minute = Int('end_minute')

# Define the meeting duration
meeting_duration = 30  # in minutes

# Define the constraints
solver = Solver()

# Meeting must be on Monday
solver.add(day == 1)

# Meeting must be between 9:00 and 17:00
solver.add(start_hour >= 9)
solver.add(start_hour < 17)
solver.add(end_hour >= 9)
solver.add(end_hour < 17)

# Meeting must be in whole hours or half hours
solver.add(Or(start_minute == 0, start_minute == 30))
solver.add(Or(end_minute == 0, end_minute == 30))

# Meeting duration is 30 minutes
solver.add(end_hour * 60 + end_minute == start_hour * 60 + start_minute + meeting_duration)

# Eric has no meetings the whole day, so no additional constraints for Eric

# Ashley's busy times: 10:00-10:30, 11:00-12:00, 12:30-13:00, 15:00-16:00
solver.add(Or(
    Or(start_hour * 60 + start_minute >= 10 * 60 + 30, end_hour * 60 + end_minute <= 10 * 60),
    Or(start_hour * 60 + start_minute >= 12 * 60, end_hour * 60 + end_minute <= 11 * 60),
    Or(start_hour * 60 + start_minute >= 13 * 60, end_hour * 60 + end_minute <= 12 * 60 + 30),
    Or(start_hour * 60 + start_minute >= 16 * 60, end_hour * 60 + end_minute <= 15 * 60)
))

# Ronald's busy times: 9:00-9:30, 10:00-11:30, 12:30-14:00, 14:30-17:00
solver.add(Or(
    Or(start_hour * 60 + start_minute >= 9 * 60 + 30, end_hour * 60 + end_minute <= 9 * 60),
    Or(start_hour * 60 + start_minute >= 11 * 60 + 30, end_hour * 60 + end_minute <= 10 * 60),
    Or(start_hour * 60 + start_minute >= 14 * 60, end_hour * 60 + end_minute <= 12 * 60 + 30),
    Or(start_hour * 60 + start_minute >= 17 * 60, end_hour * 60 + end_minute <= 14 * 60 + 30)
))

# Larry's busy times: 9:00-12:00, 13:00-17:00
solver.add(Or(
    Or(start_hour * 60 + start_minute >= 12 * 60, end_hour * 60 + end_minute <= 9 * 60),
    Or(start_hour * 60 + start_minute >= 17 * 60, end_hour * 60 + end_minute <= 13 * 60)
))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_time = f"{model[start_hour].as_long()}:{model[start_minute].as_long():02}"
    end_time = f"{model[end_hour].as_long()}:{model[end_minute].as_long():02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")