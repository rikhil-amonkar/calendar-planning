from z3 import *

# Define the variables for the meeting time
day = String('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the constraints
s = Solver()

# The meeting must be on Monday
s.add(day == "Monday")

# The meeting must be within work hours (9:00 to 17:00)
s.add(start_time >= 9 * 60)  # 9:00 in minutes
s.add(end_time <= 17 * 60)   # 17:00 in minutes

# The meeting duration is 30 minutes
s.add(end_time - start_time == 30)

# Emily's busy times
emily_busy_times = [(10 * 60, 10 * 60 + 30), (11 * 60 + 30, 12 * 60 + 30), (14 * 60, 15 * 60), (16 * 60, 16 * 60 + 30)]
for start, end in emily_busy_times:
    s.add(Or(start_time >= end, end_time <= start))

# Melissa's busy times
melissa_busy_times = [(9 * 60 + 30, 10 * 60), (14 * 60 + 30, 15 * 60)]
for start, end in melissa_busy_times:
    s.add(Or(start_time >= end, end_time <= start))

# Frank's busy times
frank_busy_times = [(10 * 60, 10 * 60 + 30), (11 * 60, 11 * 60 + 30), (12 * 60 + 30, 13 * 60 + 30), 
                    (13 * 60 + 30, 14 * 60 + 30), (15 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)]
for start, end in frank_busy_times:
    s.add(Or(start_time >= end, end_time <= start))

# Frank does not want to meet after 9:30
s.add(start_time <= 9 * 60 + 30)

# Check if there is a solution
if s.check() == sat:
    m = s.model()
    start_hour = m[start_time].as_long() // 60
    start_minute = m[start_time].as_long() % 60
    end_hour = m[end_time].as_long() // 60
    end_minute = m[end_time].as_long() % 60
    print(f"SOLUTION:\nDay: {m[day]}\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")