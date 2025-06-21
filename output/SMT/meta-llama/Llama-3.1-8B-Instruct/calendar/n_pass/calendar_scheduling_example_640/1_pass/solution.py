from z3 import *

def schedule_meeting(bobby_schedule, michael_schedule, duration):
    # Create Z3 variables for the meeting day and time
    day = Int('day')
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Define the domain of the variables
    day_domain = [0, 1]  # 0 for Monday, 1 for Tuesday
    start_time_domain = [9*60, 17*60]  # in minutes
    end_time_domain = [9*60 + duration, 17*60]

    # Define the constraints for the day
    day_constraints = [day >= 0, day <= 1]

    # Define the constraints for the start time
    start_time_constraints = [
        start_time >= 9*60,
        start_time <= 17*60,
        start_time + duration <= 17*60
    ]

    # Define the constraints for the end time
    end_time_constraints = [
        end_time >= 9*60 + duration,
        end_time <= 17*60
    ]

    # Define the constraints for Bobby's schedule
    bobby_constraints = []
    for start, end in bobby_schedule:
        start_minutes = start.hour * 60 + start.minute
        end_minutes = end.hour * 60 + end.minute
        bobby_constraints.extend([
            Or(start_time + duration > start_minutes, end_time < start_minutes),
            Or(start_time + duration > end_minutes, end_time < end_minutes)
        ])

    # Define the constraints for Michael's schedule
    michael_constraints = []
    for start, end in michael_schedule:
        start_minutes = start.hour * 60 + start.minute
        end_minutes = end.hour * 60 + end.minute
        michael_constraints.extend([
            Or(start_time + duration > start_minutes, end_time < start_minutes),
            Or(start_time + duration > end_minutes, end_time < end_minutes)
        ])

    # Define the solver and add the constraints
    solver = Solver()
    solver.add(day_constraints)
    solver.add(start_time_constraints)
    solver.add(end_time_constraints)
    solver.add(bobby_constraints)
    solver.add(michael_constraints)

    # Solve the solver
    if solver.check() == sat:
        # Get the model
        model = solver.model()
        # Extract the values from the model
        day_value = model[day].as_long()
        start_time_value = model[start_time].as_long()
        end_time_value = model[end_time].as_long()
        # Convert the values to hours and minutes
        start_hour = start_time_value // 60
        start_minute = start_time_value % 60
        end_hour = end_time_value // 60
        end_minute = end_time_value % 60
        # Print the solution
        print(f"SOLUTION:")
        print(f"Day: {'Monday' if day_value == 0 else 'Tuesday'}")
        print(f"Start Time: {start_hour:02d}:{start_minute:02d}")
        print(f"End Time: {end_hour:02d}:{end_minute:02d}")
    else:
        print("No solution found")

# Define the schedules for Bobby and Michael
bobby_schedule = [
    (Time(14, 30), Time(15, 0)),
    (Time(9, 0), Time(11, 30)),
    (Time(12, 0), Time(12, 30)),
    (Time(13, 0), Time(15, 0)),
    (Time(15, 30), Time(17, 0))
]
michael_schedule = [
    (Time(9, 0), Time(10, 0)),
    (Time(10, 30), Time(13, 30)),
    (Time(14, 0), Time(15, 0)),
    (Time(15, 30), Time(17, 0)),
    (Time(9, 0), Time(10, 30)),
    (Time(11, 0), Time(11, 30)),
    (Time(12, 0), Time(14, 0)),
    (Time(15, 0), Time(16, 0)),
    (Time(16, 30), Time(17, 0))
]

# Define the meeting duration
duration = 30

# Schedule the meeting
schedule_meeting(bobby_schedule, michael_schedule, duration)