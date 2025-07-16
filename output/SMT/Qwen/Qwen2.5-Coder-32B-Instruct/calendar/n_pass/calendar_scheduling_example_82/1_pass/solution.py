from z3 import *

# Define the time slots in minutes from 9:00 to 17:00 (9 * 60 to 17 * 60)
start_of_day = 9 * 60
end_of_day = 17 * 60
meeting_duration = 30

# Define variables for the start time of the meeting
meeting_start = Int('meeting_start')

# Create a solver instance
solver = Solver()

# Constraints for Michael
michael_busy_slots = [(9 * 60 + 30, 10 * 60 + 30), (15 * 60, 15 * 60 + 30), (16 * 60, 16 * 60 + 30)]
for busy_start, busy_end in michael_busy_slots:
    solver.add(Or(meeting_start + meeting_duration <= busy_start, meeting_start >= busy_end))

# Constraints for Eric (Eric is available all day, so no constraints needed)

# Constraints for Arthur
arthur_busy_slots = [(9 * 60, 12 * 60), (13 * 60, 15 * 60), (15 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)]
for busy_start, busy_end in arthur_busy_slots:
    solver.add(Or(meeting_start + meeting_duration <= busy_start, meeting_start >= busy_end))

# Ensure the meeting is within working hours
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
    
    print("SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {meeting_start_hour:02}:{meeting_start_minute:02}")
    print(f"End Time: {meeting_end_hour:02}:{meeting_end_minute:02}")
else:
    print("No solution found")