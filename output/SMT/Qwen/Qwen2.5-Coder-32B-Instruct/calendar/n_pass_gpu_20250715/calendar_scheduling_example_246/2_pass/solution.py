from z3 import *

# Define the time slots in minutes from 9:00 to 17:00
start_time = 9 * 60  # 9:00 AM
end_time = 17 * 60   # 5:00 PM
meeting_duration = 30  # 30 minutes

# Define the variables for the meeting start time
meeting_start = Int('meeting_start')

# Create a solver instance
solver = Solver()

# Add constraints for each participant
# Jacob is busy on Monday during 13:30 to 14:00, 14:30 to 15:00
solver.add(Or(meeting_start + meeting_duration <= 13 * 60 + 30,
             meeting_start >= 14 * 60))
solver.add(Or(meeting_start + meeting_duration <= 14 * 60 + 30,
             meeting_start >= 15 * 60))

# Diana has blocked her calendar on Monday during 9:30 to 10:00, 11:30 to 12:00, 13:00 to 13:30, 16:00 to 16:30
solver.add(Or(meeting_start + meeting_duration <= 9 * 60 + 30,
             meeting_start >= 10 * 60))
solver.add(Or(meeting_start + meeting_duration <= 11 * 60 + 30,
             meeting_start >= 12 * 60))
solver.add(Or(meeting_start + meeting_duration <= 13 * 60,
             meeting_start >= 13 * 60 + 30))
solver.add(Or(meeting_start + meeting_duration <= 16 * 60,
             meeting_start >= 16 * 60 + 30))

# Adam has meetings on Monday during 9:30 to 10:30, 11:00 to 12:30, 15:30 to 16:00
solver.add(Or(meeting_start + meeting_duration <= 9 * 60 + 30,
             meeting_start >= 10 * 60 + 30))
solver.add(Or(meeting_start + meeting_duration <= 11 * 60,
             meeting_start >= 12 * 30))
solver.add(Or(meeting_start + meeting_duration <= 15 * 30,
             meeting_start >= 16 * 0))

# Angela is busy on Monday during 9:30 to 10:00, 10:30 to 12:00, 13:00 to 15:30, 16:00 to 16:30
solver.add(Or(meeting_start + meeting_duration <= 9 * 60 + 30,
             meeting_start >= 10 * 0))
solver.add(Or(meeting_start + meeting_duration <= 10 * 30,
             meeting_start >= 12 * 0))
solver.add(Or(meeting_start + meeting_duration <= 13 * 0,
             meeting_start >= 15 * 30))
solver.add(Or(meeting_start + meeting_duration <= 16 * 0,
             meeting_start >= 16 * 30))

# Dennis has meetings on Monday during 9:00 to 9:30, 10:30 to 11:30, 13:00 to 15:00, 16:30 to 17:00
solver.add(Or(meeting_start + meeting_duration <= 9 * 60 + 30,
             meeting_start >= 9 * 60 + 30))
solver.add(Or(meeting_start + meeting_duration <= 10 * 30,
             meeting_start >= 11 * 30))
solver.add(Or(meeting_start + meeting_duration <= 13 * 0,
             meeting_start >= 15 * 0))
solver.add(Or(meeting_start + meeting_duration <= 16 * 30,
             meeting_start >= 17 * 0))

# Ensure the meeting is within working hours
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
    
    print(f"SOLUTION:")
    print(f"Day: Monday")
    print(f"Start Time: {meeting_start_hour:02}:{meeting_start_minute:02}")
    print(f"End Time: {meeting_end_hour:02}:{meeting_end_minute:02}")
else:
    print("No solution found")