from z3 import *

# Define the time slots as integers representing minutes from 9:00 AM
start_of_day = 9 * 60  # 9:00 AM
end_of_day = 17 * 60   # 5:00 PM
meeting_duration = 30  # 30 minutes

# Create a variable for the start time of the meeting
meeting_start = Int('meeting_start')

# Define the availability constraints for each participant
constraints = [
    # Andrea is available all day, so no additional constraints needed
    # Jack's busy times: 9:00-9:30, 14:00-14:30
    Or(meeting_start >= 9*60 + 30, meeting_start + meeting_duration <= 14*60),
    Or(meeting_start >= 14*60 + 30, meeting_start + meeting_duration <= 17*60),
    
    # Madison's busy times: 9:30-10:30, 13:00-14:00, 15:00-15:30, 16:30-17:00
    Or(meeting_start >= 9*60 + 30, meeting_start + meeting_duration <= 10*60 + 30),
    Or(meeting_start >= 13*60, meeting_start + meeting_duration <= 14*60),
    Or(meeting_start >= 15*60 + 30, meeting_start + meeting_duration <= 16*60),
    Or(meeting_start >= 16*60 + 30, meeting_start + meeting_duration <= 17*60),
    
    # Rachel's busy times: 9:30-10:30, 11:00-11:30, 12:00-13:30, 14:30-15:30, 16:00-17:00
    Or(meeting_start >= 9*60 + 30, meeting_start + meeting_duration <= 10*60 + 30),
    Or(meeting_start >= 11*60, meeting_start + meeting_duration <= 11*60 + 30),
    Or(meeting_start >= 12*60 + 30, meeting_start + meeting_duration <= 14*60 + 30),
    Or(meeting_start >= 14*60 + 30, meeting_start + meeting_duration <= 15*60 + 30),
    Or(meeting_start >= 16*60, meeting_start + meeting_duration <= 17*60),
    
    # Douglas's busy times: 9:00-11:30, 12:00-16:30
    Or(meeting_start >= 11*60 + 30, meeting_start + meeting_duration <= 12*60),
    Or(meeting_start >= 16*60 + 30, meeting_start + meeting_duration <= 17*60),
    
    # Ryan's busy times: 9:00-9:30, 13:00-14:00, 14:30-17:00
    Or(meeting_start >= 9*60 + 30, meeting_start + meeting_duration <= 13*60),
    Or(meeting_start >= 14*60, meeting_start + meeting_duration <= 14*60 + 30),
    Or(meeting_start >= 14*60 + 30, meeting_start + meeting_duration <= 17*60),
    
    # Meeting must be within working hours
    meeting_start >= start_of_day,
    meeting_start + meeting_duration <= end_of_day
]

# Create a solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_time = model[meeting_start].as_long()
    meeting_end_time = meeting_start_time + meeting_duration
    
    # Convert the meeting start and end times back to HH:MM format
    start_hour = meeting_start_time // 60
    start_minute = meeting_start_time % 60
    end_hour = meeting_end_time // 60
    end_minute = meeting_end_time % 60
    
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found.")