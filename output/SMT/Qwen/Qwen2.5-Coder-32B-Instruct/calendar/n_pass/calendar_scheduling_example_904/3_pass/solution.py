from z3 import *

# Define the variables
day = Int('day')
start_time = Int('start_time')

# Define the domain for day (Monday=1, Tuesday=2, Wednesday=3, Thursday=4, Friday=5)
days = [1, 2, 3, 4, 5]

# Define the domain for start_time (in minutes from 9:00)
start_times = range(540, 1020, 30)  # From 9:00 to 17:00 in 30-minute increments

# Create a solver instance
solver = Solver()

# Add constraints for Daniel's availability
for d in days:
    if d == 1:  # Monday
        solver.add(Or(start_time < 570, And(start_time >= 630, start_time < 720), And(start_time >= 780, start_time < 840), And(start_time >= 870, start_time < 930), And(start_time >= 960, start_time < 1020)))
    elif d == 2:  # Tuesday
        solver.add(Or(start_time < 660, And(start_time >= 780, start_time < 810), And(start_time >= 930, start_time < 960), And(start_time >= 1020, start_time < 1080)))
    elif d == 3:  # Wednesday
        solver.add(Or(start_time < 540, And(start_time >= 840, start_time < 870)))
    elif d == 4:  # Thursday
        solver.add(Or(start_time < 630, And(start_time >= 720, start_time < 750), And(start_time >= 870, start_time < 900), And(start_time >= 930, start_time < 960), And(start_time >= 1020, start_time < 1080)))
    elif d == 5:  # Friday
        solver.add(Or(start_time < 570, And(start_time >= 690, start_time < 720), And(start_time >= 780, start_time < 810), And(start_time >= 1020, start_time < 1080)))

# Add constraints for Bradley's availability
for d in days:
    if d == 1:  # Monday
        solver.add(Or(start_time < 570, And(start_time >= 660, start_time < 750), And(start_time >= 780, start_time < 840), And(start_time >= 870, start_time < 930), And(start_time >= 960, start_time < 1020)))
    elif d == 2:  # Tuesday
        solver.add(Or(start_time < 630, And(start_time >= 720, start_time < 750), And(start_time >= 810, start_time < 840), And(start_time >= 930, start_time < 960), And(start_time >= 1020, start_time < 1080)))
    elif d == 3:  # Wednesday
        solver.add(Or(start_time < 540, And(start_time >= 750, start_time < 840), And(start_time >= 840, start_time < 870), And(start_time >= 870, start_time < 1020)))
    elif d == 4:  # Thursday
        solver.add(Or(start_time < 750, And(start_time >= 810, start_time < 840), And(start_time >= 870, start_time < 900), And(start_time >= 930, start_time < 960), And(start_time >= 1020, start_time < 1080)))
    elif d == 5:  # Friday
        solver.add(Or(start_time < 570, And(start_time >= 720, start_time < 750), And(start_time >= 780, start_time < 810), And(start_time >= 810, start_time < 840), And(start_time >= 930, start_time < 960), And(start_time >= 1020, start_time < 1080)))

# Add preferences
solver.add(day != 3)  # Daniel does not want to meet on Wednesday
solver.add(day != 4)  # Daniel does not want to meet on Thursday
solver.add(day != 1)  # Bradley does not want to meet on Monday
solver.add(Or(day != 2, start_time >= 720))  # Bradley does not want to meet on Tuesday before 12:00
solver.add(day != 5)  # Bradley does not want to meet on Friday

# Define the meeting duration (30 minutes)
meeting_duration = 30

# Ensure the meeting ends within the work hours
solver.add(start_time + meeting_duration <= 1020)

# Ensure day is within the valid range
solver.add(day >= 1)
solver.add(day <= 5)

# Solve the problem
if solver.check() == sat:
    m = solver.model()
    meeting_day = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"][m[day].as_long() - 1]
    meeting_start_time = m[start_time].as_long()
    meeting_end_time = meeting_start_time + meeting_duration
    
    # Convert start and end times to HH:MM format
    start_time_str = f"{(meeting_start_time // 60):02}:{(meeting_start_time % 60):02}"
    end_time_str = f"{(meeting_end_time // 60):02}:{(meeting_end_time % 60):02}"
    
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")