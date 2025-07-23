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

# James's busy times
# 11:30 to 12:00
s.add(Or(start_hour < 11, start_hour >= 12, (start_hour == 11 and start_minute < 30), (start_hour == 12 and start_minute >= 0)))
# 14:30 to 15:00
s.add(Or(start_hour < 14, start_hour >= 15, (start_hour == 14 and start_minute < 30), (start_hour == 15 and start_minute >= 0)))

# John's busy times
# 9:30 to 11:00
s.add(Or(start_hour < 9, start_hour >= 11, (start_hour == 9 and start_minute < 30), (start_hour == 11 and start_minute >= 0)))
# 11:30 to 12:00
s.add(Or(start_hour < 11, start_hour >= 12, (start_hour == 11 and start_minute < 30), (start_hour == 12 and start_minute >= 0)))
# 12:30 to 13:30
s.add(Or(start_hour < 12, start_hour >= 13, (start_hour == 12 and start_minute < 30), (start_hour == 13 and start_minute >= 0)))
# 14:30 to 16:30
s.add(Or(start_hour < 14, start_hour >= 16, (start_hour == 14 and start_minute < 30), (start_hour == 16 and start_minute >= 0)))

# Check if there is a solution
if s.check() == sat:
    m = s.model()
    day_val = m[day].as_string()
    start_hour_val = m[start_hour].as_long()
    start_minute_val = m[start_minute].as_long()
    end_hour_val = m[end_hour].as_long()
    end_minute_val = m[end_minute].as_long()
    print(f"SOLUTION:\nDay: {day_val}\nStart Time: {start_hour_val:02}:{start_minute_val:02}\nEnd Time: {end_hour_val:02}:{end_minute_val:02}")
else:
    print("No solution found")