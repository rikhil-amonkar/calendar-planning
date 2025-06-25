from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time in minutes after 9:00AM
end_time = Int('end_time')  # End time in minutes after 9:00AM
meeting_time = Int('meeting_time')  # Meeting time in minutes after 9:00AM
timothy_start_time = 9 * 60 + 45  # Timothy's start time in minutes after 9:00AM
timothy_end_time = 9 * 60 + 30  # Timothy's end time in minutes after 9:00AM

# Define the constraints
s = Optimize()
s.add(start_time >= 0)  # Start time should be non-negative
s.add(end_time >= 0)  # End time should be non-negative
s.add(meeting_time >= 0)  # Meeting time should be non-negative
s.add(end_time >= start_time + 45)  # Meeting time should be at least 45 minutes
s.add(meeting_time >= start_time + 45)  # Meeting time should be at least 45 minutes
s.add(meeting_time <= end_time)  # Meeting time should be before end time
s.add(timothy_start_time <= meeting_time)  # Meeting time should be after Timothy's start time
s.add(meeting_time <= timothy_end_time)  # Meeting time should be before Timothy's end time
s.add(start_time + 12 <= end_time)  # Travel time from Alamo Square to Richmond District should be within the time frame
s.add(end_time + 13 >= meeting_time)  # Travel time from Richmond District to Alamo Square should be within the time frame

# Define the objective function
s.maximize(meeting_time - start_time)  # Maximize the meeting time

# Solve the optimization problem
result = s.check()
if result == sat:
    m = s.model()
    print(f"Best schedule: Start at {m[start_time].as_long()} minutes past 9:00AM, Meet Timothy at {m[meeting_time].as_long()} minutes past 9:00AM")
else:
    print("No solution found")