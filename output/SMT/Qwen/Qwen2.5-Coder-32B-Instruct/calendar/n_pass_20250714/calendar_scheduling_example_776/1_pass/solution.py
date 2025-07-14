from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
start_time = Int('start_time')  # in 24-hour format * 100 (e.g., 9:00 is 900)

# Define the constraints
constraints = []

# John's constraints: available all week, but prefers not after 14:30 on Monday
constraints.append(Or(day == 1, day == 2, start_time <= 1430))

# Jennifer's constraints:
# Monday: 9:00-11:00, 11:30-13:00, 13:30-14:30, 15:00-17:00
constraints.append(Or(day != 0,
                     Or(start_time >= 1100, start_time < 900),
                     Or(start_time >= 1300, start_time < 1130),
                     Or(start_time >= 1430, start_time < 1330),
                     Or(start_time >= 1700, start_time < 1500)))

# Tuesday: 9:00-11:30, 12:00-17:00
constraints.append(Or(day != 1,
                     Or(start_time >= 1130, start_time < 900),
                     Or(start_time >= 1700, start_time < 1200)))

# Wednesday: 9:00-11:30, 12:00-12:30, 13:00-14:00, 14:30-16:00, 16:30-17:00
constraints.append(Or(day != 2,
                     Or(start_time >= 1130, start_time < 900),
                     Or(start_time >= 1230, start_time < 1200),
                     Or(start_time >= 1400, start_time < 1300),
                     Or(start_time >= 1600, start_time < 1430),
                     Or(start_time >= 1700, start_time < 1630)))

# Meeting duration is 30 minutes
end_time = start_time + 30

# Meeting must be within work hours (9:00 - 17:00)
constraints.append(And(start_time >= 900, end_time <= 1700))

# Day must be one of Monday, Tuesday, or Wednesday
constraints.append(And(day >= 0, day <= 2))

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + 30
    
    # Map day value to day name
    days = ["Monday", "Tuesday", "Wednesday"]
    day_name = days[day_value]
    
    # Format the start and end times
    start_time_str = f"{start_time_value // 100}:{start_time_value % 100:02}"
    end_time_str = f"{end_time_value // 100}:{end_time_value % 100:02}"
    
    print(f"SOLUTION:\nDay: {day_name}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")