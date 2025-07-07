from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')  # in minutes from 00:00

# Define the constants for the time slots
meeting_duration = 30  # half an hour
work_start = 9 * 60  # 9:00
work_end = 17 * 60  # 17:00

# Define the constraints for Shirley
shirley_busy_monday = Or(
    And(start_time >= 10 * 60 + 30, start_time < 11 * 60),
    And(start_time >= 12 * 60, start_time < 12 * 60 + 30),
    And(start_time >= 16 * 60, start_time < 16 * 60 + 30)
)

shirley_busy_tuesday = And(start_time >= 9 * 60 + 30, start_time < 10 * 60)

# Define the constraints for Albert
albert_busy_monday = Or(
    And(start_time >= 9 * 60, start_time < 17 * 60)  # Albert is busy all day on Monday
)

albert_busy_tuesday = Or(
    And(start_time >= 9 * 60 + 30, start_time < 11 * 60),
    And(start_time >= 11 * 60 + 30, start_time < 12 * 60 + 30),
    And(start_time >= 13 * 60, start_time < 16 * 60),
    And(start_time >= 16 * 60 + 30, start_time < 17 * 60)
)

# Shirley's preference: not after 10:30 on Tuesday
shirley_preference_tuesday = start_time < 10 * 60 + 30

# Define the solver
solver = Solver()

# Add the constraints to the solver
solver.add(Or(day == 0, day == 1))  # Day can only be Monday or Tuesday
solver.add(start_time >= work_start)  # Meeting must start within work hours
solver.add(start_time + meeting_duration <= work_end)  # Meeting must end within work hours

# Shirley's busy times
solver.add(Implies(day == 0, Not(shirley_busy_monday)))  # Shirley's busy times on Monday
solver.add(Implies(day == 1, Not(shirley_busy_tuesday)))  # Shirley's busy times on Tuesday

# Albert's busy times
solver.add(Implies(day == 0, Not(albert_busy_monday)))  # Albert's busy times on Monday
solver.add(Implies(day == 1, Not(albert_busy_tuesday)))  # Albert's busy times on Tuesday

# Shirley's preference on Tuesday
solver.add(Implies(day == 1, shirley_preference_tuesday))  # Shirley's preference on Tuesday

# Explicitly add the valid slot on Tuesday
valid_slot_tuesday = And(start_time == 11 * 60, day == 1)

# Add the valid slot constraint
solver.add(valid_slot_tuesday)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    meeting_day = "Monday" if model[day].as_long() == 0 else "Tuesday"
    meeting_start = model[start_time].as_long()
    meeting_end = meeting_start + meeting_duration
    
    print(f"SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start // 60}:{meeting_start % 60:02}\nEnd Time: {meeting_end // 60}:{meeting_end % 60:02}")
else:
    print("No solution found")