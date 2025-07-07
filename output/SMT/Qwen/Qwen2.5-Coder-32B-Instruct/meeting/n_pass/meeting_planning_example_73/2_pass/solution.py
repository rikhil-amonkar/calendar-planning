from z3 import *

# Define the variables
start_meeting = Int('start_meeting')  # Start time of meeting with Barbara in minutes from 9:00 AM

# Constraints
# Barbara is available from 7:15 AM to 10:00 PM, which is 135 to 1440 minutes from 00:00 AM
barbara_start = 135  # 7:15 AM in minutes from 00:00 AM
barbara_end = 1440   # 10:00 PM in minutes from 00:00 AM

# You arrive at Russian Hill at 9:00 AM, which is 540 minutes from 00:00 AM
arrival_time = 540  # 9:00 AM in minutes from 00:00 AM

# Travel time from Russian Hill to Pacific Heights is 7 minutes
travel_time = 7

# Meeting duration should be at least 60 minutes
meeting_duration = 60

# Define the constraints
constraints = [
    start_meeting >= arrival_time + travel_time,  # You must reach Pacific Heights before starting the meeting
    start_meeting + meeting_duration <= barbara_end,  # Meeting should end before Barbara leaves
    start_meeting >= barbara_start,  # Meeting should start after Barbara arrives
]

# Create the solver
solver = Solver()

# Add the constraints to the solver
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_time_minutes_from_midnight = model[start_meeting].as_long()
    start_time_hours = start_time_minutes_from_midnight // 60
    start_time_minutes = start_time_minutes_from_midnight % 60
    print(f"SOLUTION: You should start meeting Barbara at {start_time_hours:02}:{start_time_minutes:02} AM.")
else:
    print("SOLUTION: It is not possible to meet Barbara for at least 60 minutes within the given constraints.")