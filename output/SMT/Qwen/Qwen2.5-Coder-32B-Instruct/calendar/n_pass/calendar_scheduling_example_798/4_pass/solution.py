from z3 import *

# Define variables
day = Int('day')  # 1 for Monday, 2 for Tuesday, 3 for Wednesday
start_time = Int('start_time')  # in minutes since 9:00

# Define constants for the days
MONDAY = 1
TUESDAY = 2
WEDNESDAY = 3

# Meeting duration in minutes (30 minutes)
meeting_duration = 30

# Define the constraints
constraints = []

# Day constraint: must be Monday, Tuesday, or Wednesday
constraints.append(Or(day == MONDAY, day == TUESDAY, day == WEDNESDAY))

# Time constraint: must be within work hours (9:00 to 17:00)
constraints.append(start_time >= 0)  # 0 corresponds to 9:00
constraints.append(start_time + meeting_duration <= 480)  # 480 corresponds to 17:00

# Nancy's availability
# Monday: 10:00 to 10:30, 11:30 to 12:30, 13:30 to 14:00, 14:30 to 15:30, 16:00 to 17:00
constraints.append(Or(day != MONDAY, Or(start_time < 60, start_time + meeting_duration > 90)))  # 60 corresponds to 10:00, 90 corresponds to 10:30
constraints.append(Or(day != MONDAY, Or(start_time < 90, start_time + meeting_duration > 150)))  # 90 corresponds to 11:30, 150 corresponds to 12:30
constraints.append(Or(day != MONDAY, Or(start_time < 210, start_time + meeting_duration > 270)))  # 210 corresponds to 13:30, 270 corresponds to 14:30
constraints.append(Or(day != MONDAY, Or(start_time < 270, start_time + meeting_duration > 330)))  # 270 corresponds to 14:30, 330 corresponds to 15:30
constraints.append(Or(day != MONDAY, Or(start_time < 360, start_time + meeting_duration > 480)))  # 360 corresponds to 16:00

# Tuesday: 9:30 to 10:30, 11:00 to 11:30, 12:00 to 12:30, 13:00 to 13:30, 15:30 to 16:00
constraints.append(Or(day != TUESDAY, Or(start_time < 30, start_time + meeting_duration > 60)))  # 30 corresponds to 9:30, 60 corresponds to 10:30
constraints.append(Or(day != TUESDAY, Or(start_time < 60, start_time + meeting_duration > 75)))  # 60 corresponds to 11:00, 75 corresponds to 11:30
constraints.append(Or(day != TUESDAY, Or(start_time < 75, start_time + meeting_duration > 90)))  # 75 corresponds to 12:00, 90 corresponds to 12:30
constraints.append(Or(day != TUESDAY, Or(start_time < 90, start_time + meeting_duration > 105)))  # 90 corresponds to 13:00, 105 corresponds to 13:30
constraints.append(Or(day != TUESDAY, Or(start_time < 210, start_time + meeting_duration > 300)))  # 210 corresponds to 15:30, 300 corresponds to 16:00

# Wednesday: 10:00 to 11:30, 13:30 to 16:00
constraints.append(Or(day != WEDNESDAY, Or(start_time < 60, start_time + meeting_duration > 150)))  # 60 corresponds to 10:00, 150 corresponds to 12:30
constraints.append(Or(day != WEDNESDAY, Or(start_time < 210, start_time + meeting_duration > 360)))  # 210 corresponds to 13:30, 360 corresponds to 16:00

# Jose's availability
# Monday: 9:00 to 17:00
constraints.append(Or(day != MONDAY, False))  # Jose is not available on Monday

# Tuesday: 9:00 to 17:00
constraints.append(Or(day != TUESDAY, False))  # Jose is not available on Tuesday

# Wednesday: 9:00 to 9:30, 10:00 to 12:30, 13:30 to 14:30, 15:00 to 17:00
constraints.append(Or(day != WEDNESDAY, Or(start_time < 30, start_time + meeting_duration > 30)))  # 30 corresponds to 9:30
constraints.append(Or(day != WEDNESDAY, Or(start_time < 150, start_time + meeting_duration > 150)))  # 150 corresponds to 12:30
constraints.append(Or(day != WEDNESDAY, Or(start_time < 210, start_time + meeting_duration > 270)))  # 210 corresponds to 13:30, 270 corresponds to 14:30
constraints.append(Or(day != WEDNESDAY, Or(start_time < 300, start_time + meeting_duration > 480)))  # 300 corresponds to 15:00

# Create solver instance
solver = Solver()

# Add constraints to the solver
for c in constraints:
    solver.add(c)

# Check if there is a solution
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + meeting_duration

    # Convert meeting start and end times to HH:MM format
    start_hour = 9 + meeting_start_time // 60
    start_minute = meeting_start_time % 60
    end_hour = 9 + meeting_end_time // 60
    end_minute = meeting_end_time % 60

    # Print the solution
    print(f"SOLUTION:")
    print(f"Day: {'Monday' if meeting_day == MONDAY else 'Tuesday' if meeting_day == TUESDAY else 'Wednesday'}")
    print(f"Start Time: {start_hour:02}:{start_minute:02}")
    print(f"End Time: {end_hour:02}:{end_minute:02}")
else:
    print("No solution found.")