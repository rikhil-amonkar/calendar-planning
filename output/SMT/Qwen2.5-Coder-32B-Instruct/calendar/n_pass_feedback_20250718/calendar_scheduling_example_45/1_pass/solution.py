from z3 import *

# Define the time variables
day = String('day')
start_hour = Int('start_hour')
start_minute = Int('start_minute')
end_hour = Int('end_hour')
end_minute = Int('end_minute')

# Define the constraints
solver = Solver()

# Meeting duration is 30 minutes
solver.add(end_hour * 60 + end_minute == start_hour * 60 + start_minute + 30)

# Meeting should be between 9:00 and 17:00 on Monday
solver.add(day == "Monday")
solver.add(start_hour * 60 + start_minute >= 9 * 60)
solver.add(end_hour * 60 + end_minute <= 17 * 60)

# Andrew and Grace are available the whole day, so no additional constraints for them

# Samuel's blocked times
# 9:00 to 10:30
solver.add(Or(start_hour * 60 + start_minute >= 10 * 60 + 30, end_hour * 60 + end_minute <= 9 * 60))
# 11:30 to 12:00
solver.add(Or(start_hour * 60 + start_minute >= 12 * 60, end_hour * 60 + end_minute <= 11 * 60 + 30))
# 13:00 to 13:30
solver.add(Or(start_hour * 60 + start_minute >= 13 * 60 + 30, end_hour * 60 + end_minute <= 13 * 60))
# 14:00 to 16:00
solver.add(Or(start_hour * 60 + start_minute >= 16 * 60, end_hour * 60 + end_minute <= 14 * 60))
# 16:30 to 17:00
solver.add(Or(start_hour * 60 + start_minute >= 17 * 60, end_hour * 60 + end_minute <= 16 * 60 + 30))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    start_time = f"{model[start_hour].as_long():02}:{model[start_minute].as_long():02}"
    end_time = f"{model[end_hour].as_long():02}:{model[end_minute].as_long():02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")