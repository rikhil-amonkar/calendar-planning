from z3 import *

# Define the time slots as integers representing minutes from 9:00
start_time = 9 * 60
end_time = 17 * 60
meeting_duration = 30

# Define variables for the start time of the meeting
meeting_start = Int('meeting_start')

# Define the constraints for each participant
constraints = [
    # Jose: 11:00 to 11:30, 12:30 to 13:00; cannot meet after 15:30
    Or(meeting_start < 11 * 60, meeting_start >= 11 * 60 + 30),
    Or(meeting_start < 12 * 60 + 30, meeting_start >= 13 * 60),
    meeting_start + meeting_duration <= 15 * 60 + 30,
    
    # Keith: 14:00 to 14:30, 15:00 to 15:30
    Or(meeting_start < 14 * 60, meeting_start >= 14 * 60 + 30),
    Or(meeting_start < 15 * 60, meeting_start >= 15 * 60 + 30),
    
    # Logan: 9:00 to 10:00, 12:00 to 12:30, 15:00 to 15:30
    Or(meeting_start < 9 * 60 + 30, meeting_start >= 10 * 60),
    Or(meeting_start < 12 * 60, meeting_start >= 12 * 60 + 30),
    Or(meeting_start < 15 * 60, meeting_start >= 15 * 60 + 30),
    
    # Megan: 9:00 to 10:30, 11:00 to 12:00, 13:00 to 13:30, 14:30 to 16:30
    Or(meeting_start < 9 * 60 + 30, meeting_start >= 10 * 60 + 30),
    Or(meeting_start < 11 * 60, meeting_start >= 12 * 60),
    Or(meeting_start < 13 * 60, meeting_start >= 13 * 60 + 30),
    Or(meeting_start < 14 * 60 + 30, meeting_start >= 16 * 60 + 30),
    
    # Gary: 9:00 to 9:30, 10:00 to 10:30, 11:30 to 13:00, 13:30 to 14:00, 14:30 to 16:30
    Or(meeting_start < 9 * 60 + 30, meeting_start >= 9 * 60 + 60),
    Or(meeting_start < 10 * 60 + 30, meeting_start >= 10 * 60 + 60),
    Or(meeting_start < 11 * 60 + 30, meeting_start >= 13 * 60),
    Or(meeting_start < 13 * 60 + 30, meeting_start >= 14 * 60),
    Or(meeting_start < 14 * 60 + 30, meeting_start >= 16 * 60 + 30),
    
    # Bobby: 11:00 to 11:30, 12:00 to 12:30, 13:00 to 16:00
    Or(meeting_start < 11 * 60, meeting_start >= 11 * 60 + 30),
    Or(meeting_start < 12 * 60, meeting_start >= 12 * 60 + 30),
    Or(meeting_start < 13 * 60, meeting_start >= 16 * 60),
    
    # Meeting must be within working hours
    meeting_start >= start_time,
    meeting_start + meeting_duration <= end_time
]

# Create a solver instance and add the constraints
solver = Solver()
solver.add(constraints)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_minutes = model[meeting_start].as_long()
    meeting_start_time = f"{meeting_start_minutes // 60:02}:{meeting_start_minutes % 60:02}"
    meeting_end_time = f"{(meeting_start_minutes + meeting_duration) // 60:02}:{(meeting_start_minutes + meeting_duration) % 60:02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {meeting_start_time}\nEnd Time: {meeting_end_time}")
else:
    print("No solution found")