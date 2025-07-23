from z3 import *

# Define the variables
day = Int('day')  # 0 = Monday, 1 = Tuesday, 2 = Wednesday
start_time = Int('start_time')  # in minutes from 00:00

# Define the constraints
meeting_duration = 30  # 30 minutes

# Define the work hours
work_start = 9 * 60  # 9:00 in minutes
work_end = 17 * 60  # 17:00 in minutes

# Define the days
monday = 0
tuesday = 1
wednesday = 2

# John's constraints
john_availability = And(
    Or(day == monday, day == tuesday, day == wednesday),
    Or(
        And(day == monday, start_time >= work_start, start_time + meeting_duration <= 14 * 60),  # Monday before 14:30
        And(day == tuesday, start_time >= work_start, start_time + meeting_duration <= work_end),  # Tuesday all day
        And(day == wednesday, start_time >= work_start, start_time + meeting_duration <= work_end)  # Wednesday all day
    )
)

# Jennifer's constraints
jennifer_availability = And(
    Or(day == monday, day == tuesday, day == wednesday),
    Or(
        And(day == monday, Or(
            And(start_time >= 11 * 60 + 30, start_time + meeting_duration <= 13 * 60),  # Monday 11:30 - 13:00
            And(start_time >= 14 * 60 + 30, start_time + meeting_duration <= 15 * 60)   # Monday 14:30 - 15:00
        )),
        And(day == tuesday, Or(
            And(start_time >= 11 * 60 + 30, start_time + meeting_duration <= 12 * 00)  # Tuesday 11:30 - 12:00
        )),
        And(day == wednesday, Or(
            And(start_time >= 11 * 60 + 30, start_time + meeting_duration <= 12 * 00),  # Wednesday 11:30 - 12:00
            And(start_time >= 12 * 60 + 30, start_time + meeting_duration <= 13 * 00),  # Wednesday 12:30 - 13:00
            And(start_time >= 14 * 60, start_time + meeting_duration <= 14 * 60 + 30),  # Wednesday 14:00 - 14:30
            And(start_time >= 16 * 60 + 30, start_time + meeting_duration <= 17 * 00)   # Wednesday 16:30 - 17:00
        ))
    )
)

# Combine all constraints
constraints = And(
    john_availability,
    jennifer_availability,
    start_time >= work_start,
    start_time + meeting_duration <= work_end
)

# Create a solver and add the constraints
solver = Solver()
solver.add(constraints)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    meeting_day = model[day].as_long()
    meeting_start_time = model[start_time].as_long()
    meeting_end_time = meeting_start_time + meeting_duration

    # Convert times to HH:MM format
    def format_time(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"

    # Determine the day name
    day_name = ["Monday", "Tuesday", "Wednesday"][meeting_day]

    # Print the solution
    print(f"SOLUTION:")
    print(f"Day: {day_name}")
    print(f"Start Time: {format_time(meeting_start_time)}")
    print(f"End Time: {format_time(meeting_end_time)}")
else:
    print("No solution found")