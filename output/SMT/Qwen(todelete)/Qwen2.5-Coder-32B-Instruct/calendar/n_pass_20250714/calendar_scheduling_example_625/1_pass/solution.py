from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes since 9:00

# Define the constants for the problem
meeting_duration = 30  # 30 minutes
work_start = 0  # 9:00 in minutes since 9:00
work_end = 480  # 17:00 in minutes since 9:00

# Constraints for Jeffrey (free all week)
# No specific constraints for Jeffrey, so no additional constraints needed

# Constraints for Harold
harold_monday_busy = Or(And(start_time >= 0, start_time + meeting_duration <= 60),  # 9:00 - 10:00
                         And(start_time >= 63, start_time + meeting_duration <= 480))  # 10:30 - 17:00
harold_tuesday_busy = Or(And(start_time >= 0, start_time + meeting_duration <= 18),  # 9:00 - 9:30
                          And(start_time >= 63, start_time + meeting_duration <= 69),  # 10:30 - 11:30
                          And(start_time >= 138, start_time + meeting_duration <= 158),  # 12:30 - 13:30
                          And(start_time >= 218, start_time + meeting_duration <= 238),  # 14:30 - 15:30
                          And(start_time >= 360, start_time + meeting_duration <= 480))  # 16:00 - 17:00

# Harold's preference to avoid Monday
avoid_monday = day != 0

# Harold's preference to avoid before 14:30 on Tuesday
tuesday_after_1430 = Or(day != 1, start_time >= 330)  # 14:30 in minutes since 9:00

# Define the solver
solver = Solver()

# Add constraints to the solver
solver.add(Or(day == 0, day == 1))  # Day can only be Monday or Tuesday
solver.add(start_time >= work_start)  # Meeting must start after work start
solver.add(start_time + meeting_duration <= work_end)  # Meeting must end before work end
solver.add(Not(harold_monday_busy))  # Harold must be free on Monday
solver.add(Not(harold_tuesday_busy))  # Harold must be free on Tuesday
solver.add(avoid_monday)  # Harold prefers not to meet on Monday
solver.add(tuesday_after_1430)  # Harold prefers not to meet before 14:30 on Tuesday

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
    meeting_start_time_minutes = model[start_time].as_long()
    meeting_start_time = f"{9 + meeting_start_time_minutes // 60}:{meeting_start_time_minutes % 60:02}"
    meeting_end_time = f"{9 + (meeting_start_time_minutes + meeting_duration) // 60}:{(meeting_start_time_minutes + meeting_duration) % 60:02}"
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_time}\nEnd Time: {meeting_end_time}")
else:
    print("No solution found")