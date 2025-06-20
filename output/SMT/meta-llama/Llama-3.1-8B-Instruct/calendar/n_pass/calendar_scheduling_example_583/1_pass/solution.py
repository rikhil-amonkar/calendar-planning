from z3 import *

def schedule_meeting(lisa_schedule, anthony_schedule, meeting_duration):
    # Create Z3 variables for the day and time
    day = Int('day')
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Create Z3 variables for Lisa and Anthony's availability
    lisa_available = [Int(f'lisa_available_{i}') for i in range(len(lisa_schedule))]
    anthony_available = [Int(f'anthony_available_{i}') for i in range(len(anthony_schedule))]

    # Define the constraints
    constraints = [
        day == 0,  # The day is Monday
        And(start_time >= 9, start_time <= 17),  # The start time is between 9:00 and 17:00
        And(end_time >= 9, end_time <= 17),  # The end time is between 9:00 and 17:00
        start_time + meeting_duration <= end_time,  # The meeting duration is half an hour
        Or([lisa_available[i] for i in range(len(lisa_schedule))]),  # Lisa is available
        Or([anthony_available[i] for i in range(len(anthony_schedule))]),  # Anthony is available
    ]

    # Add the constraints for Lisa's schedule
    for i, (start, end) in enumerate(lisa_schedule):
        constraints.append(Not(And(start <= start_time, end > start_time)))
        constraints.append(Not(And(start <= end_time, end > end_time)))

    # Add the constraints for Anthony's schedule
    for i, (start, end) in enumerate(anthony_schedule):
        constraints.append(Not(And(start <= start_time, end > start_time)))
        constraints.append(Not(And(start <= end_time, end > end_time)))

    # Create the Z3 solver and add the constraints
    solver = Solver()
    solver.add(constraints)

    # Solve the constraints
    if solver.check() == sat:
        model = solver.model()
        # Extract the solution
        day_val = model[day].as_long()
        start_time_val = model[start_time].as_long()
        end_time_val = model[end_time].as_long()

        # Return the solution as a string
        return f"SOLUTION:\nDay: {['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'][day_val]}\nStart Time: {start_time_val:02d}:00\nEnd Time: {end_time_val:02d}:00"
    else:
        return "No solution found"

# Define the schedules and meeting duration
lisa_schedule = [(9, 9.5), (10.5, 11), (14, 16)]
anthony_schedule = [(9, 9.5), (11, 11.5), (12.5, 13.5), (14, 15), (15.5, 16), (16.5, 17)]
meeting_duration = 30

# Print the solution
print(schedule_meeting(lisa_schedule, anthony_schedule, meeting_duration))