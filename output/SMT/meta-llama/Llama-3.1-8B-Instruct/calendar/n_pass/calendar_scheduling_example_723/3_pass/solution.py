from z3 import *

def schedule_meeting(arthur_schedule, michael_schedule, day_constraints, meeting_duration):
    # Define the days of the week
    days = ['Monday', 'Tuesday', 'Wednesday']

    # Create Z3 variables for the meeting day, start time, and end time
    day = Int('day')
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Add constraints for the meeting day
    day_constraints = [day == day_index for day_index, day in enumerate(days) if day in day_constraints]
    day_constraints = Or(day_constraints)

    # Add constraints for the meeting start and end time
    start_time_constraints = [start_time >= 9, start_time <= 17]
    end_time_constraints = [end_time >= start_time + meeting_duration, end_time <= 17]

    # Add constraints for the meeting duration
    duration_constraints = [end_time - start_time == meeting_duration]

    # Add constraints for Arthur's schedule
    arthur_constraints = []
    for start, end in arthur_schedule:
        arthur_constraints.append(Not(And(And(start_time >= start, start_time <= end), And(end_time >= start, end_time <= end))))
    arthur_constraints = Or(arthur_constraints)

    # Add constraints for Michael's schedule
    michael_constraints = []
    for start, end in michael_schedule:
        michael_constraints.append(Not(And(And(start_time >= start, start_time <= end), And(end_time >= start, end_time <= end))))
    michael_constraints = Or(michael_constraints)

    # Arthur cannot meet on Tuesday
    arthur_constraints = And(arthur_constraints, Or(day!= 1))

    # Create the Z3 solver
    solver = Solver()

    # Add all constraints to the solver
    solver.add(day_constraints)
    solver.add(start_time_constraints)
    solver.add(end_time_constraints)
    solver.add(duration_constraints)
    solver.add(arthur_constraints)
    solver.add(michael_constraints)

    # Solve the constraints
    if solver.check() == sat:
        # Get the model
        model = solver.model()
        # Extract the meeting day, start time, and end time
        meeting_day = days[model[day].as_long()]
        meeting_start_time = model[start_time].as_long()
        meeting_end_time = model[end_time].as_long()
        # Return the solution
        return f'SOLUTION:\nDay: {meeting_day}\nStart Time: {meeting_start_time:02d}:{meeting_start_time % 60:02d}\nEnd Time: {meeting_end_time:02d}:{meeting_end_time % 60:02d}'
    else:
        return 'No solution found'

# Define the existing schedules for Arthur and Michael
arthur_schedule = [(30, 60), (210, 240), (300, 330), (180, 210), (360, 390), (420, 450), (300, 330), (360, 390), (420, 450), (360, 390)]
michael_schedule = [(180, 300), (210, 240), (300, 330), (450, 570), (270, 570), (330, 420), (270, 390), (360, 420), (540, 570)]

# Define the day constraints
day_constraints = ['Monday', 'Wednesday']

# Define the meeting duration
meeting_duration = 30

print(schedule_meeting(arthur_schedule, michael_schedule, day_constraints, meeting_duration))