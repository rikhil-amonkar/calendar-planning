from z3 import *

# Define the variables for the meeting time
day = String('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the meeting duration
meeting_duration = 30

# Define the constraints
solver = Solver()

# All meetings must be between 9:00 and 17:00 on Monday
solver.add(day == "Monday")
solver.add(start_time >= 9 * 60)  # 9:00 in minutes
solver.add(end_time <= 17 * 60)   # 17:00 in minutes
solver.add(end_time == start_time + meeting_duration)

# Lisa's busy times
lisa_busy_times = [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60 + 30), (12 * 60 + 30, 13 * 60), (16 * 60, 16 * 60 + 30)]
for start, end in lisa_busy_times:
    solver.add(Or(end_time <= start, start_time >= end))

# Bobby's busy times
bobby_busy_times = [(9 * 60, 9 * 60 + 30), (10 * 60, 10 * 60 + 30), (11 * 60 + 30, 12 * 60), (15 * 60, 15 * 60 + 30)]
for start, end in bobby_busy_times:
    solver.add(Or(end_time <= start, start_time >= end))
# Bobby prefers not to have meetings after 15:00
solver.add(end_time <= 15 * 60)

# Randy's busy times
randy_busy_times = [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 11 * 60), (11 * 60 + 30, 12 * 60 + 30), 
                    (13 * 60, 13 * 60 + 30), (14 * 60 + 30, 15 * 60 + 30), (16 * 60, 16 * 60 + 30)]
for start, end in randy_busy_times:
    solver.add(Or(end_time <= start, start_time >= end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_hour = model[start_time].as_long() // 60
    start_minute = model[start_time].as_long() % 60
    end_hour = model[end_time].as_long() // 60
    end_minute = model[end_time].as_long() % 60
    print(f"SOLUTION:\nDay: {model[day]}\nStart Time: {start_hour:02}:{start_minute:02}\nEnd Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")