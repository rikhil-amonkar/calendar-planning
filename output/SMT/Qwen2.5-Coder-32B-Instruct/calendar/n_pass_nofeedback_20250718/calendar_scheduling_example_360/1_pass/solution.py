from z3 import *

# Define the time slots in minutes from 9:00 to 17:00
start_time = 9 * 60  # 9:00 in minutes
end_time = 17 * 60   # 17:00 in minutes
meeting_duration = 30  # 30 minutes

# Define the meeting time variable
meeting_start = Int('meeting_start')

# Create a solver instance
solver = Solver()

# Add constraints for each participant
# Emily: 10:00 to 10:30, 16:00 to 16:30
solver.add(Or(meeting_start + meeting_duration <= 10 * 60, meeting_start >= 10 * 60 + 30))
solver.add(Or(meeting_start + meeting_duration <= 16 * 60, meeting_start >= 16 * 60 + 30))

# Mason: Free the entire day
# No constraints needed for Mason

# Maria: 10:30 to 11:00, 14:00 to 14:30
solver.add(Or(meeting_start + meeting_duration <= 10 * 60 + 30, meeting_start >= 11 * 60))
solver.add(Or(meeting_start + meeting_duration <= 14 * 60, meeting_start >= 14 * 60 + 30))

# Carl: 9:30 to 10:00, 10:30 to 12:30, 13:30 to 14:00, 14:30 to 15:30, 16:00 to 17:00
solver.add(Or(meeting_start + meeting_duration <= 9 * 60 + 30, meeting_start >= 10 * 60))
solver.add(Or(meeting_start + meeting_duration <= 10 * 60 + 30, meeting_start >= 12 * 60 + 30))
solver.add(Or(meeting_start + meeting_duration <= 13 * 60 + 30, meeting_start >= 14 * 60))
solver.add(Or(meeting_start + meeting_duration <= 14 * 60 + 30, meeting_start >= 15 * 60 + 30))
solver.add(Or(meeting_start + meeting_duration <= 16 * 60, meeting_start >= 17 * 60))

# David: 9:30 to 11:00, 11:30 to 12:00, 12:30 to 13:30, 14:00 to 15:00, 16:00 to 17:00
solver.add(Or(meeting_start + meeting_duration <= 9 * 60 + 30, meeting_start >= 11 * 60))
solver.add(Or(meeting_start + meeting_duration <= 11 * 60 + 30, meeting_start >= 12 * 60))
solver.add(Or(meeting_start + meeting_duration <= 12 * 60 + 30, meeting_start >= 13 * 60 + 30))
solver.add(Or(meeting_start + meeting_duration <= 14 * 60, meeting_start >= 15 * 60))
solver.add(Or(meeting_start + meeting_duration <= 16 * 60, meeting_start >= 17 * 60))

# Frank: 9:30 to 10:30, 11:00 to 11:30, 12:30 to 13:30, 14:30 to 17:00
solver.add(Or(meeting_start + meeting_duration <= 9 * 60 + 30, meeting_start >= 10 * 60 + 30))
solver.add(Or(meeting_start + meeting_duration <= 11 * 60, meeting_start >= 11 * 60 + 30))
solver.add(Or(meeting_start + meeting_duration <= 12 * 60 + 30, meeting_start >= 13 * 60 + 30))
solver.add(Or(meeting_start + meeting_duration <= 14 * 60 + 30, meeting_start >= 17 * 60))

# Meeting must be within work hours
solver.add(meeting_start >= start_time)
solver.add(meeting_start + meeting_duration <= end_time)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_minutes = model[meeting_start].as_long()
    meeting_start_time = f"{meeting_start_minutes // 60:02}:{meeting_start_minutes % 60:02}"
    meeting_end_time = f"{(meeting_start_minutes + meeting_duration) // 60:02}:{(meeting_start_minutes + meeting_duration) % 60:02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {meeting_start_time}\nEnd Time: {meeting_end_time}")
else:
    print("No solution found")