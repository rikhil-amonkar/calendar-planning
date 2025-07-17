from z3 import *

# Define the time variables
day = Int('day')
start_time = Int('start_time')
end_time = Int('end_time')

# Define the meeting duration
meeting_duration = 30  # in minutes

# Define the constraints for each participant
constraints = []

# Daniel is free the whole day
# No additional constraints needed for Daniel

# Kathleen is busy from 14:30 to 15:30
constraints.append(Or(start_time >= 1530, end_time <= 1430))

# Carolyn is busy from 12:00 to 12:30 and 13:00 to 13:30
constraints.append(Or(start_time >= 1230, end_time <= 1200))
constraints.append(Or(start_time >= 1330, end_time <= 1300))

# Roger is free the entire day, but prefers not to meet before 12:30
constraints.append(start_time >= 1230)

# Cheryl is busy from 9:00 to 9:30, 10:00 to 11:30, 12:30 to 13:30, 14:00 to 17:00
constraints.append(Or(start_time >= 930, end_time <= 900))
constraints.append(Or(start_time >= 1130, end_time <= 1000))
constraints.append(Or(start_time >= 1330, end_time <= 1230))
constraints.append(Or(start_time >= 1700, end_time <= 1400))

# Virginia is busy from 9:30 to 11:30, 12:00 to 12:30, 13:00 to 13:30, 14:30 to 15:30, 16:00 to 17:00
constraints.append(Or(start_time >= 1130, end_time <= 930))
constraints.append(Or(start_time >= 1230, end_time <= 1200))
constraints.append(Or(start_time >= 1330, end_time <= 1300))
constraints.append(Or(start_time >= 1530, end_time <= 1430))
constraints.append(Or(start_time >= 1700, end_time <= 1600))

# Angela is busy from 9:30 to 10:00, 10:30 to 11:30, 12:00 to 12:30, 13:00 to 13:30, 14:00 to 16:30
constraints.append(Or(start_time >= 1000, end_time <= 930))
constraints.append(Or(start_time >= 1130, end_time <= 1030))
constraints.append(Or(start_time >= 1230, end_time <= 1200))
constraints.append(Or(start_time >= 1330, end_time <= 1300))
constraints.append(Or(start_time >= 1630, end_time <= 1400))

# General constraints for the meeting time
constraints.append(day == 1)  # Monday
constraints.append(start_time >= 900)  # Start time is at least 9:00
constraints.append(end_time <= 1700)  # End time is at most 17:00
constraints.append(end_time == start_time + meeting_duration)  # Meeting duration is 30 minutes

# Ensure start_time and end_time are valid times in 24-hour format
constraints.append(start_time % 100 < 60)
constraints.append(end_time % 100 < 60)

# Create the solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_time_value = model[start_time].as_long()
    end_time_value = model[end_time].as_long()
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time_value // 100}:{start_time_value % 100:02}\nEnd Time: {end_time_value // 100}:{end_time_value % 100:02}")
else:
    print("No solution found")