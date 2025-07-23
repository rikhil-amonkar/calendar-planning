from z3 import *

# Define the time slots in minutes from 9:00 to 17:00
start_of_day = 9 * 60  # 9:00 in minutes
end_of_day = 17 * 60   # 17:00 in minutes
meeting_duration = 30  # 30 minutes

# Define the variables for the start time of the meeting
meeting_start = Int('meeting_start')

# Create a solver instance
solver = Solver()

# Add constraints for Michael's availability
solver.add(meeting_start < start_of_day + 30 * 60)  # Before 12:30
solver.add(meeting_start + meeting_duration > start_of_day + 60 * 60)  # After 10:30
solver.add(meeting_start < start_of_day + 90 * 60)  # Before 13:30
solver.add(meeting_start + meeting_duration > start_of_day + 150 * 60)  # After 15:30
solver.add(meeting_start < start_of_day + 180 * 60)  # Before 16:30
solver.add(meeting_start + meeting_duration > start_of_day + 210 * 60)  # After 16:30

# Eric is available all day, so no additional constraints for him

# Add constraints for Arthur's availability
solver.add(meeting_start < start_of_day + 30 * 60)  # Before 9:30
solver.add(meeting_start + meeting_duration > start_of_day + 120 * 60)  # After 12:00
solver.add(meeting_start < start_of_day + 150 * 60)  # Before 13:30
solver.add(meeting_start + meeting_duration > start_of_day + 180 * 60)  # After 15:00
solver.add(meeting_start < start_of_day + 210 * 60)  # Before 15:30
solver.add(meeting_start + meeting_duration > start_of_day + 240 * 60)  # After 16:00
solver.add(meeting_start < start_of_day + 270 * 60)  # Before 16:30
solver.add(meeting_start + meeting_duration > start_of_day + 300 * 60)  # After 17:00

# Ensure the meeting is within work hours
solver.add(meeting_start >= start_of_day)
solver.add(meeting_start + meeting_duration <= end_of_day)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_time = model[meeting_start].as_long()
    meeting_start_hour = meeting_start_time // 60
    meeting_start_minute = meeting_start_time % 60
    meeting_end_time = meeting_start_time + meeting_duration
    meeting_end_hour = meeting_end_time // 60
    meeting_end_minute = meeting_end_time % 60

    print(f"SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {meeting_start_hour:02}:{meeting_start_minute:02}")
    print(f"End Time: {meeting_end_hour:02}:{meeting_end_minute:02}")
else:
    print("No solution found")