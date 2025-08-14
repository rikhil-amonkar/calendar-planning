from z3 import *

# Define the variables for the day and time
day = Int('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constants for the days
MONDAY = 0
TUESDAY = 1
WEDNESDAY = 2

# Meeting duration is 30 minutes
meeting_duration = 30

# Define the constraints for each person's availability
def is_available(person, d, t):
    if person == 'Tyler':
        if d == MONDAY:
            return Or(t < 60 * 9, t >= 60 * 16)  # 9:00 to 16:00 is not available
        elif d == TUESDAY:
            return And(t >= 60 * 9 + 30, t + meeting_duration <= 60 * 14 + 30) | \
                   And(t >= 60 * 15, t + meeting_duration <= 60 * 17)  # 9:30 to 14:30 and 15:00 to 17:00 are available
        elif d == WEDNESDAY:
            return And(t >= 60 * 9, t < 60 * 10 + 30) | \
                   And(t >= 60 * 11 + 30, t < 60 * 12 + 30) | \
                   And(t >= 60 * 13 + 30, t < 60 * 14 + 30) | \
                   And(t >= 60 * 15, t < 60 * 16 + 30)  # 9:00 to 10:30, 11:30 to 12:30, 13:30 to 14:30, 15:00 to 16:30 are available
    elif person == 'Ruth':
        if d == MONDAY:
            return And(t >= 60 * 10 + 30, t + meeting_duration <= 60 * 12 + 30) | \
                   And(t >= 60 * 14 + 30, t + meeting_duration <= 60 * 15)  # 10:30 to 12:30 and 14:30 to 15:00 are available
        elif d == TUESDAY:
            return False  # Not available all day
        elif d == WEDNESDAY:
            return False  # Not available all day
    return True

# Create the solver
solver = Solver()

# Add the constraints for the day and time
solver.add(day >= 0)
solver.add(day <= 2)
solver.add(start_time >= 0)
solver.add(start_time + meeting_duration <= 8 * 60)  # 8 hours from 9:00 to 17:00

# Add the constraints for availability
solver.add(is_available('Tyler', day, start_time))
solver.add(is_available('Ruth', day, start_time))

# Add the preference for Tyler to avoid meetings on Monday before 16:00
solver.add(Or(day != MONDAY, start_time >= 60 * 16))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + meeting_duration

    # Convert the day value to a string
    day_str = ["Monday", "Tuesday", "Wednesday"][day_value]

    # Convert the start and end times to HH:MM format
    start_time_str = f"{(start_time_value // 60 + 9):02}:{(start_time_value % 60):02}"
    end_time_str = f"{(end_time_value // 60 + 9):02}:{(end_time_value % 60):02}"

    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")