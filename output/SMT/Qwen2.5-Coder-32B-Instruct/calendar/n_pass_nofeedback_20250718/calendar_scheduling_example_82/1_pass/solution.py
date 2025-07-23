from z3 import *

# Define the time slots in minutes from 9:00 to 17:00
start_of_day = 9 * 60  # 9:00 in minutes
end_of_day = 17 * 60   # 17:00 in minutes
meeting_duration = 30  # 30 minutes

# Define the variables for the start time of the meeting
meeting_start = Int('meeting_start')

# Create a solver instance
solver = Solver()

# Add constraints for Michael's schedule
solver.add(meeting_start < start_of_day + 30 * 60)  # Before 12:30
solver.add(meeting_start + meeting_duration > start_of_day + 60 * 60)  # After 10:30
solver.add(meeting_start < start_of_day + 90 * 60)  # Before 13:30
solver.add(meeting_start + meeting_duration > start_of_day + 120 * 60)  # After 15:00
solver.add(meeting_start < start_of_day + 120 * 60)  # Before 16:00
solver.add(meeting_start + meeting_duration > start_of_day + 150 * 60)  # After 16:30

# Eric's calendar is wide open, so no constraints for Eric

# Add constraints for Arthur's schedule
solver.add(meeting_start < start_of_day + 30 * 60)  # Before 11:30
solver.add(meeting_start + meeting_duration > start_of_day + 120 * 60)  # After 12:00
solver.add(meeting_start < start_of_day + 90 * 60)  # Before 14:30
solver.add(meeting_start + meeting_duration > start_of_day + 150 * 60)  # After 15:00
solver.add(meeting_start < start_of_day + 120 * 60)  # Before 16:00
solver.add(meeting_start + meeting_duration > start_of_day + 180 * 60)  # After 16:30

# Ensure the meeting is within work hours
solver.add(meeting_start >= start_of_day)
solver.add(meeting_start + meeting_duration <= end_of_day)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_minutes = model[meeting_start].as_long()
    meeting_start_time = f"{(meeting_start_minutes // 60):02}:{(meeting_start_minutes % 60):02}"
    meeting_end_time = f"{((meeting_start_minutes + meeting_duration) // 60):02}:{((meeting_start_minutes + meeting_duration) % 60):02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {meeting_start_time}\nEnd Time: {meeting_end_time}")
else:
    print("No solution found")