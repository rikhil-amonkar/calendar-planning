from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
constraints = []

# Define the meeting duration
meeting_duration = 30  # 30 minutes

# Define the work hours
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60  # 17:00 in minutes

# Define the days
days = 3  # Monday, Tuesday, Wednesday

# Nicole's busy times
nicole_busy_times = [
    (0, 9 * 60, 9 * 60 + 30),  # Monday 9:00 to 9:30
    (0, 13 * 60, 13 * 60 + 30),  # Monday 13:00 to 13:30
    (0, 14 * 60 + 30, 15 * 60 + 30),  # Monday 14:30 to 15:30
    (1, 9 * 60, 9 * 60 + 30),  # Tuesday 9:00 to 9:30
    (1, 11 * 60 + 30, 13 * 60 + 30),  # Tuesday 11:30 to 13:30
    (1, 14 * 60 + 30, 15 * 60 + 30),  # Tuesday 14:30 to 15:30
    (2, 10 * 60, 11 * 60),  # Wednesday 10:00 to 11:00
    (2, 12 * 60 + 30, 15 * 60),  # Wednesday 12:30 to 15:00
    (2, 16 * 60, 17 * 60)  # Wednesday 16:00 to 17:00
]

# Ruth's busy times
ruth_busy_times = [
    (0, 9 * 60, 17 * 60),  # Monday 9:00 to 17:00
    (1, 9 * 60, 17 * 60),  # Tuesday 9:00 to 17:00
    (2, 9 * 60, 10 * 60 + 30),  # Wednesday 9:00 to 10:30
    (2, 11 * 60, 11 * 60 + 30),  # Wednesday 11:00 to 11:30
    (2, 12 * 60, 12 * 60 + 30),  # Wednesday 12:00 to 12:30
    (2, 13 * 60 + 30, 15 * 60 + 30),  # Wednesday 13:30 to 15:30
    (2, 16 * 60, 16 * 60 + 30)  # Wednesday 16:00 to 16:30
]

# Ruth's preference: do not meet on Wednesday after 13:30
ruth_preference = (2, 13 * 60 + 30, 17 * 60)

# Constraints for the day
constraints.append(day >= 0)
constraints.append(day < days)

# Constraints for the start time
constraints.append(start_time >= work_start)
constraints.append(start_time + meeting_duration <= work_end)

# Constraints for Nicole's busy times
for d, s, e in nicole_busy_times:
    constraints.append(Or(day != d, start_time + meeting_duration <= s, start_time >= e))

# Constraints for Ruth's busy times
for d, s, e in ruth_busy_times:
    constraints.append(Or(day != d, start_time + meeting_duration <= s, start_time >= e))

# Constraint for Ruth's preference
constraints.append(Or(day != 2, start_time + meeting_duration <= ruth_preference[1]))

# Solve the constraints
solver = Solver()
solver.add(constraints)

if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + meeting_duration

    # Convert times back to HH:MM format
    def format_time(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"

    day_str = ["Monday", "Tuesday", "Wednesday"][meeting_day]
    start_time_str = format_time(meeting_start_time)
    end_time_str = format_time(meeting_end_time)

    print(f"SOLUTION:\nDay: {day_str}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")