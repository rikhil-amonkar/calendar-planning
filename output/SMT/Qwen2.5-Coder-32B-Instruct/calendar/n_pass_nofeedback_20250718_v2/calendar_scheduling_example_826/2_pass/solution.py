from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
constraints = []

# Work hours are from 9:00 to 17:00, so start_time should be between 0 and 480 (10 hours * 60 minutes)
constraints.append(start_time >= 0)
constraints.append(start_time <= 480 - 30)  # Ensure there's room for a 30-minute meeting

# Meeting duration is 30 minutes
meeting_duration = 30

# Cheryl's calendar is wide open, so no additional constraints for her

# James's schedule
# Monday: 9:00-9:30, 10:30-11:00, 12:30-13:00, 14:30-15:30, 16:30-17:00
constraints.append(Or(start_time >= 30, start_time + meeting_duration <= 30))  # 9:00-9:30
constraints.append(Or(start_time >= 60, start_time + meeting_duration <= 60))  # 10:00-10:30
constraints.append(Or(start_time >= 90, start_time + meeting_duration <= 90))  # 10:30-11:00
constraints.append(Or(start_time >= 180, start_time + meeting_duration <= 180))  # 12:00-12:30
constraints.append(Or(start_time >= 210, start_time + meeting_duration <= 210))  # 12:30-13:00
constraints.append(Or(start_time >= 330, start_time + meeting_duration <= 330))  # 14:30-15:00
constraints.append(Or(start_time >= 360, start_time + meeting_duration <= 360))  # 15:00-15:30
constraints.append(Or(start_time >= 450, start_time + meeting_duration <= 450))  # 16:30-17:00

# Tuesday: 9:00-11:00, 11:30-12:00, 12:30-15:30, 16:00-17:00
constraints.append(Or(day != 1, Or(start_time >= 120, start_time + meeting_duration <= 120)))  # 10:00-10:30
constraints.append(Or(day != 1, Or(start_time >= 150, start_time + meeting_duration <= 150)))  # 11:00-11:30
constraints.append(Or(day != 1, Or(start_time >= 180, start_time + meeting_duration <= 180)))  # 12:00-12:30
constraints.append(Or(day != 1, Or(start_time >= 330, start_time + meeting_duration <= 330)))  # 14:30-15:00
constraints.append(Or(day != 1, Or(start_time >= 420, start_time + meeting_duration <= 420)))  # 16:00-16:30

# Wednesday: 10:00-11:00, 12:00-13:00, 13:30-16:00
constraints.append(Or(day != 2, Or(start_time >= 60, start_time + meeting_duration <= 60)))  # 10:00-10:30
constraints.append(Or(day != 2, Or(start_time >= 120, start_time + meeting_duration <= 120)))  # 11:00-11:30
constraints.append(Or(day != 2, Or(start_time >= 180, start_time + meeting_duration <= 180)))  # 12:00-12:30
constraints.append(Or(day != 2, Or(start_time >= 210, start_time + meeting_duration <= 210)))  # 13:00-13:30
constraints.append(Or(day != 2, Or(start_time >= 360, start_time + meeting_duration <= 360)))  # 15:00-15:30

# Thursday: 9:30-11:30, 12:00-12:30, 13:00-13:30, 14:00-14:30, 16:30-17:00
constraints.append(Or(day != 3, Or(start_time >= 30, start_time + meeting_duration <= 30)))  # 9:00-9:30
constraints.append(Or(day != 3, Or(start_time >= 180, start_time + meeting_duration <= 180)))  # 12:00-12:30
constraints.append(Or(day != 3, Or(start_time >= 210, start_time + meeting_duration <= 210)))  # 13:00-13:30
constraints.append(Or(day != 3, Or(start_time >= 240, start_time + meeting_duration <= 240)))  # 14:00-14:30
constraints.append(Or(day != 3, Or(start_time >= 450, start_time + meeting_duration <= 450)))  # 16:30-17:00

# Cheryl would rather not meet on Wednesday or Thursday
constraints.append(day != 2)
constraints.append(day != 3)

# Solve the constraints
solver = Solver()
solver.add(constraints)

if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + meeting_duration

    # Convert day and time to human-readable format
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    start_time_str = f"{9 + start_time_value // 60:02}:{start_time_value % 60:02}"
    end_time_str = f"{9 + end_time_value // 60:02}:{end_time_value % 60:02}"

    print(f"SOLUTION:\nDay: {days[day_value]}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")