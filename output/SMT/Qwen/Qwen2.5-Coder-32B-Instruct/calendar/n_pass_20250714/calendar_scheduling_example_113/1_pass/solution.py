from z3 import *

# Define the variables for the meeting time
day = Int('day')
start_hour = Int('start_hour')
start_minute = Int('start_minute')
end_hour = Int('end_hour')
end_minute = Int('end_minute')

# Meeting duration is 30 minutes
meeting_duration = 30

# Define the constraints
constraints = []

# Constraints for the day (only Monday is considered here)
constraints.append(day == 1)

# Constraints for the time range (9:00 to 17:00)
constraints.append(start_hour >= 9)
constraints.append(start_hour < 17)
constraints.append(end_hour >= 9)
constraints.append(end_hour <= 17)

# Convert start and end times to minutes from the start of the day for easier comparison
start_time_minutes = start_hour * 60 + start_minute
end_time_minutes = end_hour * 60 + end_minute

# Meeting duration constraint
constraints.append(end_time_minutes - start_time_minutes == meeting_duration)

# Bradley's constraints
constraints.append(Or(start_time_minutes >= 630, end_time_minutes <= 570))  # 9:30 to 10:00
constraints.append(Or(start_time_minutes >= 750, end_time_minutes <= 780))  # 12:30 to 13:00
constraints.append(Or(start_time_minutes >= 810, end_time_minutes <= 810))  # 13:30 to 14:00
constraints.append(Or(start_time_minutes >= 930, end_time_minutes <= 930))  # 15:30 to 16:00

# Teresa's constraints
constraints.append(Or(start_time_minutes >= 630, end_time_minutes <= 630))  # 10:30 to 11:00
constraints.append(Or(start_time_minutes >= 720, end_time_minutes <= 720))  # 12:00 to 12:30
constraints.append(Or(start_time_minutes >= 780, end_time_minutes <= 780))  # 13:00 to 13:30
constraints.append(Or(start_time_minutes >= 870, end_time_minutes <= 870))  # 14:30 to 15:00

# Elizabeth's constraints
constraints.append(Or(start_time_minutes >= 570, end_time_minutes <= 570))  # 9:00 to 9:30
constraints.append(Or(start_time_minutes >= 630, end_time_minutes <= 690))  # 10:30 to 11:30
constraints.append(Or(start_time_minutes >= 780, end_time_minutes <= 780))  # 13:00 to 13:30
constraints.append(Or(start_time_minutes >= 870, end_time_minutes <= 870))  # 14:30 to 15:00
constraints.append(Or(start_time_minutes >= 930, end_time_minutes <= 1020)) # 15:30 to 17:00

# Christian's constraints
constraints.append(Or(start_time_minutes >= 570, end_time_minutes <= 570))  # 9:00 to 9:30
constraints.append(Or(start_time_minutes >= 630, end_time_minutes <= 1020)) # 10:30 to 17:00

# Solve the constraints
solver = Solver()
solver.add(constraints)

if solver.check() == sat:
    model = solver.model()
    start_h = model[start_hour].as_long()
    start_m = model[start_minute].as_long()
    end_h = model[end_hour].as_long()
    end_m = model[end_minute].as_long()
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_h:02}:{start_m:02}\nEnd Time: {end_h:02}:{end_m:02}")
else:
    print("No solution found")