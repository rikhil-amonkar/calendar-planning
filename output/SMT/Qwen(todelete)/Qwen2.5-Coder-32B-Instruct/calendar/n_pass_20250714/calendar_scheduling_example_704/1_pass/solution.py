from z3 import *

# Define variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define constants for the days
MONDAY = 0
TUESDAY = 1
WEDNESDAY = 2

# Meeting duration in minutes (half an hour)
meeting_duration = 30

# Constraints for Larry and Samuel
# Larry is available all week, so no constraints for him

# Samuel's busy times in minutes from 9:00
samuel_busy_times = {
    MONDAY: [(10*60 + 30, 11*60), (12*60, 12*60 + 30), (13*60, 15*60), (15*60 + 30, 16*60 + 30)],
    TUESDAY: [(9*60, 12*60), (14*60, 15*60 + 30), (16*60 + 30, 17*60)],
    WEDNESDAY: [(10*60 + 30, 11*60), (11*60 + 30, 12*60), (12*60 + 30, 13*60), (14*60, 14*60 + 30), (15*60, 16*60)]
}

# Convert start_time to HH:MM format
def format_time(minutes):
    hours = 9 + minutes // 60
    minutes = minutes % 60
    return f"{hours:02}:{minutes:02}"

# Create solver instance
solver = Solver()

# Constraints for the day
solver.add(day >= 0)
solver.add(day <= 2)

# Constraints for the start time
solver.add(start_time >= 0)
solver.add(start_time + meeting_duration <= 8*60)  # 8 hours of working day (9:00 to 17:00)

# Add constraints to avoid Samuel's busy times
for d in range(3):
    for busy_start, busy_end in samuel_busy_times[d]:
        solver.add(Or(start_time + meeting_duration <= busy_start, start_time >= busy_end))

# Preference constraints
# Larry would rather not meet on Wednesday
solver.add(day != WEDNESDAY)

# Samuel would like to avoid more meetings on Tuesday
solver.add(day != TUESDAY)

# Find the earliest possible meeting time
solver.minimize(start_time)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    meeting_day = ["Monday", "Tuesday", "Wednesday"][model[day].as_long()]
    meeting_start = model[start_time].as_long()
    meeting_end = meeting_start + meeting_duration
    print("SOLUTION:")
    print(f"Day: {meeting_day}")
    print(f"Start Time: {format_time(meeting_start)}")
    print(f"End Time: {format_time(meeting_end)}")
else:
    print("No solution found")