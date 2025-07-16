from z3 import *

# Define the time slots from 9:00 to 17:00 in 30-minute increments
time_slots = [9.0, 9.5, 10.0, 10.5, 11.0, 11.5, 12.0, 12.5, 13.0, 13.5, 14.0, 14.5, 15.0, 15.5, 16.0, 16.5]

# Define variables for the start time of the meeting
start_time = Real('start_time')

# Create a solver instance
solver = Solver()

# Add constraints for each person's availability
# Bradley's blocked times: 9:30-10:00, 12:30-13:00, 13:30-14:00, 15:30-16:00
solver.add(Or(start_time < 9.5, start_time >= 10.0))
solver.add(Or(start_time < 12.5, start_time >= 13.0))
solver.add(Or(start_time < 13.5, start_time >= 14.0))
solver.add(Or(start_time < 15.5, start_time >= 16.0))

# Teresa's blocked times: 10:30-11:00, 12:00-12:30, 13:00-13:30, 14:30-15:00
solver.add(Or(start_time < 10.5, start_time >= 11.0))
solver.add(Or(start_time < 12.0, start_time >= 12.5))
solver.add(Or(start_time < 13.0, start_time >= 13.5))
solver.add(Or(start_time < 14.5, start_time >= 15.0))

# Elizabeth's blocked times: 9:00-9:30, 10:30-11:30, 13:00-13:30, 14:30-15:00, 15:30-17:00
solver.add(Or(start_time < 9.0, start_time >= 9.5))
solver.add(Or(start_time < 10.5, start_time >= 11.5))
solver.add(Or(start_time < 13.0, start_time >= 13.5))
solver.add(Or(start_time < 14.5, start_time >= 15.0))
solver.add(Or(start_time < 15.5, start_time >= 17.0))

# Christian's blocked times: 9:00-9:30, 10:30-17:00
solver.add(Or(start_time < 9.0, start_time >= 9.5))
solver.add(Or(start_time < 10.5, start_time >= 17.0))

# Meeting duration is 0.5 hours (30 minutes)
meeting_duration = 0.5

# Ensure the meeting ends before 17:00
solver.add(start_time + meeting_duration <= 17.0)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_hour = int(model[start_time].as_decimal().split('.')[0])
    start_minute = int(model[start_time].as_decimal().split('.')[1][:2])
    end_hour = start_hour + (start_minute + 30) // 60
    end_minute = (start_minute + 30) % 60
    
    # Format the start and end times
    start_time_formatted = f"{start_hour:02}:{start_minute:02}"
    end_time_formatted = f"{end_hour:02}:{end_minute:02}"
    
    # Print the solution
    print(f"SOLUTION:\nDay: Monday\nStart Time: {start_time_formatted}\nEnd Time: {end_time_formatted}")
else:
    print("No solution found")