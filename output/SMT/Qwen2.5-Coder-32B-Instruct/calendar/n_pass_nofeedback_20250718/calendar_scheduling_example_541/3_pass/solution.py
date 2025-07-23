from z3 import *

# Define the time variables
day = String('day')
start_hour = Int('start_hour')
start_minute = Int('start_minute')
end_hour = Int('end_hour')
end_minute = Int('end_minute')

# Define the constraints
s = Solver()

# Meeting duration is 1 hour
s.add(end_hour == start_hour + 1)
s.add(end_minute == start_minute)

# Meeting should be between 9:00 and 17:00 on Monday
s.add(day == "Monday")
s.add(start_hour >= 9)
s.add(start_hour < 17)
s.add(start_minute >= 0)
s.add(start_minute < 60)

# Kayla's blocked times
# 10:00 to 10:30
s.add(Or(start_hour < 10, end_hour > 10, Or(start_hour > 10, end_hour <= 10, start_minute >= 30)))
# 14:30 to 16:00
s.add(Or(start_hour < 14, end_hour > 16, Or(start_hour > 14, end_hour <= 16, start_minute >= 30)))

# Rebecca's blocked times
# 9:00 to 13:00
s.add(Or(start_hour < 9, end_hour > 13, Or(start_hour > 9, end_hour <= 13, start_minute >= 0)))
# 13:30 to 15:00
s.add(Or(start_hour < 13, end_hour > 15, Or(start_hour > 13, end_hour <= 15, start_minute >= 30)))
# 15:30 to 16:00
s.add(Or(start_hour < 15, end_hour > 16, Or(start_hour > 15, end_hour <= 16, start_minute >= 30)))

# Check if there is a solution
if s.check() == sat:
    m = s.model()
    start_time = f"{m[start_hour].as_long()}:{m[start_minute].as_long():02}"
    end_time = f"{m[end_hour].as_long()}:{m[end_minute].as_long():02}"
    print(f"SOLUTION:\nDay: {m[day]}\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")