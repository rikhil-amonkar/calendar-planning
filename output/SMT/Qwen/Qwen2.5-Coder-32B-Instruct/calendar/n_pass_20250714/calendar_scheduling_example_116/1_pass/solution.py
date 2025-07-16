from z3 import *

# Define the time slots in minutes from 9:00 to 17:00
start_time = 9 * 60  # 9:00 in minutes
end_time = 17 * 60   # 17:00 in minutes
meeting_duration = 30  # 30 minutes

# Define variables for the meeting start time
meeting_start = Int('meeting_start')

# Create a solver instance
solver = Solver()

# Add constraints for each participant
# Adam: 14:00 to 15:00 (840 to 900 minutes)
solver.add(Or(meeting_start + meeting_duration <= 840, meeting_start >= 900))

# John: 13:00 to 13:30 (780 to 810 minutes), 14:00 to 14:30 (840 to 870 minutes), 15:30 to 16:00 (930 to 960 minutes), 16:30 to 17:00 (990 to 1020 minutes)
solver.add(Or(meeting_start + meeting_duration <= 780, meeting_start >= 810))
solver.add(Or(meeting_start + meeting_duration <= 840, meeting_start >= 870))
solver.add(Or(meeting_start + meeting_duration <= 930, meeting_start >= 960))
solver.add(Or(meeting_start + meeting_duration <= 990, meeting_start >= 1020))

# Stephanie: 9:30 to 10:00 (570 to 600 minutes), 10:30 to 11:00 (630 to 660 minutes), 11:30 to 16:00 (690 to 960 minutes), 16:30 to 17:00 (990 to 1020 minutes)
solver.add(Or(meeting_start + meeting_duration <= 570, meeting_start >= 600))
solver.add(Or(meeting_start + meeting_duration <= 630, meeting_start >= 660))
solver.add(Or(meeting_start + meeting_duration <= 690, meeting_start >= 960))
solver.add(Or(meeting_start + meeting_duration <= 990, meeting_start >= 1020))

# Anna: 9:30 to 10:00 (570 to 600 minutes), 12:00 to 12:30 (720 to 750 minutes), 13:00 to 15:30 (780 to 930 minutes), 16:30 to 17:00 (990 to 1020 minutes)
solver.add(Or(meeting_start + meeting_duration <= 570, meeting_start >= 600))
solver.add(Or(meeting_start + meeting_duration <= 720, meeting_start >= 750))
solver.add(Or(meeting_start + meeting_duration <= 780, meeting_start >= 930))
solver.add(Or(meeting_start + meeting_duration <= 990, meeting_start >= 1020))

# Anna's preference: not before 14:30 (870 minutes)
solver.add(meeting_start >= 870)

# Meeting time must be within working hours
solver.add(meeting_start >= start_time)
solver.add(meeting_start + meeting_duration <= end_time)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_minutes = model[meeting_start].as_long()
    meeting_start_hour = meeting_start_minutes // 60
    meeting_start_minute = meeting_start_minutes % 60
    meeting_end_minutes = meeting_start_minutes + meeting_duration
    meeting_end_hour = meeting_end_minutes // 60
    meeting_end_minute = meeting_end_minutes % 60
    
    print(f"SOLUTION:\nDay: Monday\nStart Time: {meeting_start_hour:02}:{meeting_start_minute:02}\nEnd Time: {meeting_end_hour:02}:{meeting_end_minute:02}")
else:
    print("No solution found")