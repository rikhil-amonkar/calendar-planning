from z3 import *

# Define the variables for the day, start hour, and start minute
day = Int('day')
start_hour = Int('start_hour')
start_minute = Int('start_minute')

# Define the duration of the meeting
meeting_duration = 30

# Define the constraints
solver = Solver()

# Day constraint: must be Monday, Tuesday, or Wednesday
solver.add(Or(day == 1, day == 2, day == 3))  # 1: Monday, 2: Tuesday, 3: Wednesday

# Work hours constraint: between 9:00 and 17:00
solver.add(start_hour >= 9)
solver.add(start_hour < 17)
solver.add(Or(start_minute == 0, start_minute == 30))

# Tyler's availability
# Busy on Tuesday from 9:00 to 9:30, 14:30 to 15:00
# Busy on Wednesday from 10:30 to 11:00, 12:30 to 13:00, 13:30 to 14:00, 16:30 to 17:00
solver.add(Not(And(day == 2, start_hour == 9, start_minute == 0)))
solver.add(Not(And(day == 2, start_hour == 14, start_minute == 30)))
solver.add(Not(And(day == 3, start_hour == 10, start_minute == 30)))
solver.add(Not(And(day == 3, start_hour == 12, start_minute == 30)))
solver.add(Not(And(day == 3, start_hour == 13, start_minute == 30)))
solver.add(Not(And(day == 3, start_hour == 16, start_minute == 30)))

# Ruth's availability
# Blocked on Monday from 9:00 to 10:00, 10:30 to 12:00, 12:30 to 14:30, 15:00 to 16:00, 16:30 to 17:00
# Blocked on Tuesday and Wednesday all day
solver.add(Not(And(day == 1, start_hour == 9)))
solver.add(Not(And(day == 1, start_hour == 10, start_minute == 0)))
solver.add(Not(And(day == 1, start_hour == 10, start_minute == 30)))
solver.add(Not(And(day == 1, start_hour == 12, start_minute == 0)))
solver.add(Not(And(day == 1, start_hour == 12, start_minute == 30)))
solver.add(Not(And(day == 1, start_hour == 14, start_minute == 30)))
solver.add(Not(And(day == 1, start_hour == 15)))
solver.add(Not(And(day == 1, start_hour == 16, start_minute == 0)))
solver.add(Not(And(day == 1, start_hour == 16, start_minute == 30)))
solver.add(Not(day == 2))
solver.add(Not(day == 3))

# Tyler's preference: avoid meetings on Monday before 16:00
solver.add(Or(day != 1, start_hour * 60 + start_minute >= 16 * 60))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_hour_value = model[start_hour].as_long()
    start_minute_value = model[start_minute].as_long()
    
    # Convert day number to name
    day_name = {1: "Monday", 2: "Tuesday", 3: "Wednesday"}[day_value]
    
    # Format the start and end times
    start_time = f"{start_hour_value:02}:{start_minute_value:02}"
    end_hour = start_hour_value + (start_minute_value + meeting_duration) // 60
    end_minute = (start_minute_value + meeting_duration) % 60
    end_time = f"{end_hour:02}:{end_minute:02}"
    
    print(f"SOLUTION:\nDay: {day_name}\nStart Time: {start_time}\nEnd Time: {end_time}")
else:
    print("No solution found")