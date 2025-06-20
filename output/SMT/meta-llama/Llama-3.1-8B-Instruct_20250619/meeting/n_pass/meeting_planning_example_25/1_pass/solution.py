from z3 import *

# Define the variables
start_time = Int('start_time')  # Start time in minutes after 9:00AM
meeting_duration = Int('meeting_duration')  # Meeting duration in minutes

# Define the constraints
s = Optimize()
s.add(start_time >= 0)  # Start time must be non-negative
s.add(meeting_duration >= 105)  # Meeting duration must be at least 105 minutes
s.add(start_time + meeting_duration <= 660)  # Meeting duration must not exceed 11 hours
s.add(start_time + meeting_duration >= 240)  # Meeting duration must start after 4:00PM
s.add(meeting_duration <= 9 * 60 - (start_time - 9 * 60))  # Meeting duration must not exceed the remaining time before 9:45PM
s.add(start_time + 23 <= 9 * 60)  # Travel to Chinatown must not exceed the remaining time before 9:00AM
s.add(start_time + 23 + meeting_duration + 23 <= 9 * 60 + 9 * 60 + 45)  # Travel to Chinatown and meeting must not exceed the remaining time before 9:45PM

# Define the objective function
s.minimize(1)  # Minimize the start time

# Solve the problem
result = s.check()
if result == sat:
    model = s.model()
    print("Best schedule:")
    print(f"Start time: {model[start_time]} minutes after 9:00AM")
    print(f"Meeting duration: {model[meeting_duration]} minutes")
else:
    print("No solution found")