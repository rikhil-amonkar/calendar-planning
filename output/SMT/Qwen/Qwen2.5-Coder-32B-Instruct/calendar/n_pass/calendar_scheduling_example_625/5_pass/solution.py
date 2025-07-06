from z3 import *

# Define variables
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes since 9:00

# Constants for time conversion
minutes_per_hour = 60
meeting_duration = 30  # 30 minutes

# Constraints for Jeffrey (free all week, no specific constraints)
# Constraints for Harold
harold_monday_busy = Or(
    And(start_time >= 0, start_time + meeting_duration <= 30),  # 9:00 - 10:00
    And(start_time >= 63, start_time + meeting_duration <= 480)   # 10:30 - 17:00
)

harold_tuesday_busy = Or(
    And(start_time >= 0, start_time + meeting_duration <= 30),  # 9:00 - 9:30
    And(start_time >= 63, start_time + meeting_duration <= 78),  # 10:30 - 11:30
    And(start_time >= 153, start_time + meeting_duration <= 213), # 12:30 - 13:30
    And(start_time >= 273, start_time + meeting_duration <= 333), # 14:30 - 15:30
    And(start_time >= 360, start_time + meeting_duration <= 480)  # 16:00 - 17:00
)

# Harold's preference: avoid Monday, prefer Tuesday before 14:30
harold_avoid_monday = day != 0
harold_prefer_tuesday_before_1430 = Or(day != 1, start_time + meeting_duration <= 330)  # 14:30 in minutes

# Constraints for the meeting time
meeting_within_work_hours = And(start_time >= 0, start_time + meeting_duration <= 480)  # 9:00 - 17:00

# Explicitly exclude the time slot from 9:00 to 9:30 on Tuesday
tuesday_excluded_slot = Or(day != 1, start_time >= 30)

# Create the solver
solver = Solver()

# Add constraints
solver.add(
    Or(day == 0, day == 1),  # Either Monday or Tuesday
    meeting_within_work_hours,
    Not(harold_monday_busy),
    Not(harold_tuesday_busy),
    harold_avoid_monday,
    harold_prefer_tuesday_before_1430,
    tuesday_excluded_slot
)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
    meeting_start_time_minutes = model[start_time].as_long()
    meeting_start_time = f"{9 + meeting_start_time_minutes // 60}:{meeting_start_time_minutes % 60:02}"
    meeting_end_time_minutes = meeting_start_time_minutes + meeting_duration
    meeting_end_time = f"{9 + meeting_end_time_minutes // 60}:{meeting_end_time_minutes % 60:02}"
    
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_time}\nEnd Time: {meeting_end_time}")
else:
    print("No solution found")