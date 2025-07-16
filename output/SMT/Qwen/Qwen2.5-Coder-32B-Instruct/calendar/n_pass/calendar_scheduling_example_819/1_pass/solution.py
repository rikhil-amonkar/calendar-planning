from z3 import *

# Define the variables for the day and time
day = Int('day')  # Monday=0, Tuesday=1, Wednesday=2, Thursday=3
start_time = Int('start_time')  # in minutes from 00:00

# Define the constraints
constraints = []

# Days are from 0 to 3 (Monday to Thursday)
constraints.append(day >= 0)
constraints.append(day <= 3)

# Meeting duration is 30 minutes
meeting_duration = 30

# Convert the preferred time range to minutes from 00:00
def time_to_minutes(hour, minute):
    return hour * 60 + minute

# Work hours are from 9:00 to 17:00 (540 to 1020 minutes from 00:00)
work_start = time_to_minutes(9, 0)
work_end = time_to_minutes(17, 0)

# Meeting must be within work hours
constraints.append(start_time >= work_start)
constraints.append(start_time + meeting_duration <= work_end)

# Ruth's availability
# Monday, Tuesday, Wednesday: 9:00 to 17:00 (unavailable)
# Thursday: 9:00 to 11:00, 11:30 to 14:30, 15:00 to 17:00 (unavailable)
thursday_unavailable = [
    (time_to_minutes(9, 0), time_to_minutes(11, 0)),
    (time_to_minutes(11, 30), time_to_minutes(14, 30)),
    (time_to_minutes(15, 0), time_to_minutes(17, 0))
]

# Add constraints for Ruth's unavailability
for d in range(3):  # Monday to Wednesday
    constraints.append(Or(day != d, Or(start_time + meeting_duration <= work_start, start_time >= work_end)))

for start, end in thursday_unavailable:
    constraints.append(Or(day != 3, Or(start_time + meeting_duration <= start, start_time >= end)))

# Julie's preference: avoid meetings before 11:30 on Thursday
julie_avoid_before = time_to_minutes(11, 30)
constraints.append(Or(day != 3, start_time >= julie_avoid_before))

# Solve the constraints
solver = Solver()
solver.add(constraints)

if solver.check() == sat:
    model = solver.model()
    meeting_day = ["Monday", "Tuesday", "Wednesday", "Thursday"][model[day].as_long()]
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + meeting_duration

    print(f"SOLUTION:")
    print(f"Day: {meeting_day}")
    print(f"Start Time: {meeting_start_time // 60:02}:{meeting_start_time % 60:02}")
    print(f"End Time: {meeting_end_time // 60:02}:{meeting_end_time % 60:02}")
else:
    print("No solution found")