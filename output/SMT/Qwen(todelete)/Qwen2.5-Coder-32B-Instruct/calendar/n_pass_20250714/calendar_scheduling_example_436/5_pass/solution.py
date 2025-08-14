from z3 import *

# Define the time slots in minutes from 9:00 to 17:00
start_time = 9 * 60
end_time = 17 * 60

# Define the duration of the meeting in minutes (30 minutes)
meeting_duration = 30

# Define the variables for the start time of the meeting
meeting_start = Int('meeting_start')

# Create a solver instance
solver = Solver()

# Add constraints for each person's availability
# Patrick: 13:30 to 14:00, 14:30 to 15:00
solver.add(Or(meeting_start + meeting_duration <= 13 * 60 + 30, meeting_start >= 14 * 60))
solver.add(Or(meeting_start + meeting_duration <= 14 * 60 + 30, meeting_start >= 15 * 60))

# Shirley: 9:00 to 9:30, 11:00 to 11:30, 12:00 to 12:30, 14:30 to 15:00, 16:00 to 17:00
solver.add(Or(meeting_start + meeting_duration <= 9 * 60 + 30, meeting_start >= 9 * 60 + 30))
solver.add(Or(meeting_start + meeting_duration <= 11 * 60, meeting_start >= 11 * 60 + 30))
solver.add(Or(meeting_start + meeting_duration <= 12 * 60, meeting_start >= 12 * 60 + 30))
solver.add(Or(meeting_start + meeting_duration <= 14 * 60 + 30, meeting_start >= 15 * 60))
solver.add(Or(meeting_start + meeting_duration <= 16 * 60, meeting_start >= 17 * 60))

# Jeffrey: 9:00 to 9:30, 10:30 to 11:00, 11:30 to 12:00, 13:00 to 13:30, 16:00 to 17:00
solver.add(Or(meeting_start + meeting_duration <= 9 * 60 + 30, meeting_start >= 9 * 60 + 30))
solver.add(Or(meeting_start + meeting_duration <= 10 * 60 + 30, meeting_start >= 11 * 60))
solver.add(Or(meeting_start + meeting_duration <= 11 * 60 + 30, meeting_start >= 12 * 60))
solver.add(Or(meeting_start + meeting_duration <= 13 * 60, meeting_start >= 13 * 60 + 30))
solver.add(Or(meeting_start + meeting_duration <= 16 * 60, meeting_start >= 17 * 60))

# Gloria: 11:30 to 12:00, 15:00 to 15:30
solver.add(Or(meeting_start + meeting_duration <= 11 * 60 + 30, meeting_start >= 12 * 60))
solver.add(Or(meeting_start + meeting_duration <= 15 * 60, meeting_start >= 15 * 60 + 30))

# Nathan: 9:00 to 9:30, 10:30 to 12:00, 14:00 to 17:00
solver.add(Or(meeting_start + meeting_duration <= 9 * 60 + 30, meeting_start >= 9 * 60 + 30))
solver.add(Or(meeting_start + meeting_duration <= 10 * 60 + 30, meeting_start >= 12 * 60))
solver.add(Or(meeting_start + meeting_duration <= 14 * 60, meeting_start >= 17 * 60))

# Angela: 9:00 to 9:30, 10:00 to 11:00, 12:30 to 15:00, 15:30 to 16:30
solver.add(Or(meeting_start + meeting_duration <= 9 * 60 + 30, meeting_start >= 9 * 60 + 30))
solver.add(Or(meeting_start + meeting_duration <= 10 * 60, meeting_start >= 11 * 60))
solver.add(Or(meeting_start + meeting_duration <= 12 * 60 + 30, meeting_start >= 15 * 60))
solver.add(Or(meeting_start + meeting_duration <= 15 * 60 + 30, meeting_start >= 16 * 60 + 30))

# David: 9:00 to 9:30, 10:00 to 10:30, 11:00 to 14:00, 14:30 to 16:30
solver.add(Or(meeting_start + meeting_duration <= 9 * 60 + 30, meeting_start >= 9 * 60 + 30))
solver.add(Or(meeting_start + meeting_duration <= 10 * 60 + 30, meeting_start >= 10 * 60 + 30))
solver.add(Or(meeting_start + meeting_duration <= 11 * 60, meeting_start >= 14 * 60))
solver.add(Or(meeting_start + meeting_duration <= 14 * 60 + 30, meeting_start >= 16 * 60 + 30))

# Ensure the meeting is within the working hours
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