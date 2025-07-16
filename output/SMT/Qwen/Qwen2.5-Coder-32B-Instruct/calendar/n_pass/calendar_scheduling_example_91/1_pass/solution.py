from z3 import *

# Define the variables
day = "Monday"
meeting_start = Int('meeting_start')
meeting_duration = 60  # Meeting duration in minutes

# Define the available time slots for each participant
danielle_unavailable = [(9*60, 10*60), (10*60 + 30, 11*60), (14*60 + 30, 15*60), (15*60 + 30, 16*60), (16*60 + 30, 17*60)]
bruce_unavailable = [(11*60, 11*60 + 30), (12*60 + 30, 13*60), (14*60, 14*60 + 30), (15*60 + 30, 16*60)]
eric_unavailable = [(9*60, 9*60 + 30), (10*60, 11*60), (11*60 + 30, 13*60), (14*60 + 30, 15*60 + 30)]

# Create a solver instance
solver = Solver()

# Add constraints for the meeting start time
solver.add(meeting_start >= 9*60)  # Start time must be after 9:00
solver.add(meeting_start + meeting_duration <= 17*60)  # End time must be before 17:00

# Add constraints for each participant's unavailability
for start, end in danielle_unavailable:
    solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

for start, end in bruce_unavailable:
    solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

for start, end in eric_unavailable:
    solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    start_time_minutes = model[meeting_start].as_long()
    start_hour = start_time_minutes // 60
    start_minute = start_time_minutes % 60
    end_hour = (start_time_minutes + meeting_duration) // 60
    end_minute = (start_time_minutes + meeting_duration) % 60
    
    print(f"SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found")