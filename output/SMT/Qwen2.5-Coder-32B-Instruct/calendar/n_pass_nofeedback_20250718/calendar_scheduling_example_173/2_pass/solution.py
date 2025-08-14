from z3 import *

# Define the time slots in minutes from 9:00 to 17:00
start_time = 9 * 60  # 9:00 in minutes
end_time = 17 * 60   # 17:00 in minutes
meeting_duration = 30  # 30 minutes

# Create a solver instance
solver = Solver()

# Define the meeting start time as a variable
meeting_start = Int('meeting_start')

# Constraints for the meeting time
solver.add(meeting_start >= start_time)
solver.add(meeting_start + meeting_duration <= end_time)

# Constraints for each participant's availability
# Jacqueline: 9:00-9:30, 11:00-11:30, 12:30-13:00, 15:30-16:00
solver.add(Or(meeting_start + meeting_duration <= 9 * 60 + 30,
              And(meeting_start >= 9 * 60 + 30, meeting_start + meeting_duration <= 11 * 60),
              And(meeting_start >= 11 * 60 + 30, meeting_start + meeting_duration <= 12 * 60 + 30),
              And(meeting_start >= 13 * 60, meeting_start + meeting_duration <= 15 * 60 + 30),
              meeting_start >= 16 * 60))

# Harold: 10:00-10:30, 13:00-13:30, 15:00-17:00 and Harold does not want to meet after 13:00
solver.add(Or(meeting_start + meeting_duration <= 10 * 60 + 30,
              And(meeting_start >= 10 * 60 + 30, meeting_start + meeting_duration <= 13 * 60),
              meeting_start >= 15 * 60))
solver.add(meeting_start + meeting_duration <= 13 * 60)

# Arthur: 9:00-9:30, 10:00-12:30, 14:30-15:00, 15:30-17:00
solver.add(Or(meeting_start + meeting_duration <= 9 * 60 + 30,
              And(meeting_start >= 9 * 60 + 30, meeting_start + meeting_duration <= 10 * 60),
              And(meeting_start >= 12 * 60 + 30, meeting_start + meeting_duration <= 14 * 60 + 30),
              And(meeting_start >= 15 * 60, meeting_start + meeting_duration <= 15 * 60 + 30),
              meeting_start >= 17 * 60))

# Kelly: 9:00-9:30, 10:00-11:00, 11:30-12:30, 14:00-15:00, 15:30-16:00
solver.add(Or(meeting_start + meeting_duration <= 9 * 60 + 30,
              And(meeting_start >= 9 * 60 + 30, meeting_start + meeting_duration <= 10 * 60),
              And(meeting_start >= 11 * 60, meeting_start + meeting_duration <= 11 * 60 + 30),
              And(meeting_start >= 12 * 60 + 30, meeting_start + meeting_duration <= 14 * 60),
              And(meeting_start >= 15 * 60, meeting_start + meeting_duration <= 15 * 60 + 30),
              meeting_start >= 16 * 60))

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_start_minutes = model[meeting_start].as_long()
    meeting_start_time = f"{meeting_start_minutes // 60:02}:{meeting_start_minutes % 60:02}"
    meeting_end_time = f"{(meeting_start_minutes + meeting_duration) // 60:02}:{(meeting_start_minutes + meeting_duration) % 60:02}"
    print(f"SOLUTION:\nDay: Monday\nStart Time: {meeting_start_time}\nEnd Time: {meeting_end_time}")
else:
    print("No solution found")