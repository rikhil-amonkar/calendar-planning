from z3 import *

def schedule_meeting():
    # Define the variables
    day = [Bool('day_monday'), Bool('day_tuesday')]
    start_time = [Int('start_time_monday'), Int('start_time_tuesday')]
    end_time = [Int('end_time_monday'), Int('end_time_tuesday')]

    # Define the constraints
    # Margaret's constraints
    margaret_monday_constraints = [
        Or(start_time[0] < 9, start_time[0] > 11),
        Or(start_time[0] < 13, start_time[0] > 13.5),
        Or(start_time[0] < 15, start_time[0] > 16.5)
    ]
    margaret_tuesday_constraints = [
        start_time[1] > 12,
        start_time[1] < 12.5
    ]

    # Alexis' constraints
    alexis_monday_constraints = [
        Or(start_time[0] < 9, start_time[0] > 11.5),
        Or(start_time[0] < 12.5, start_time[0] > 13),
        start_time[0] < 14,
        start_time[0] > 14.5
    ]
    alexis_tuesday_constraints = [
        Or(start_time[1] < 9, start_time[1] > 9.5),
        Or(start_time[1] < 10, start_time[1] > 10.5),
        start_time[1] < 14,
        start_time[1] > 14.5,
        start_time[1] < 16.5
    ]

    # Meeting duration constraints
    meeting_duration = 0.5  # half an hour in hours
    margaret_constraints = [
        (start_time[0] - 9) / 0.5 > 0,
        (17 - start_time[0]) / 0.5 > 0,
        (start_time[1] - 9) / 0.5 > 0,
        (17 - start_time[1]) / 0.5 > 0
    ]
    alexis_constraints = [
        (start_time[0] - 9) / 0.5 > 0,
        (start_time[0] - 9.5) / 0.5 > 0,
        (11.5 - start_time[0]) / 0.5 > 0,
        (13 - start_time[0]) / 0.5 > 0,
        (14 - start_time[0]) / 0.5 > 0,
        (14.5 - start_time[0]) / 0.5 > 0,
        (17 - start_time[0]) / 0.5 > 0,
        (start_time[1] - 9) / 0.5 > 0,
        (start_time[1] - 9.5) / 0.5 > 0,
        (10.5 - start_time[1]) / 0.5 > 0,
        (14 - start_time[1]) / 0.5 > 0,
        (14.5 - start_time[1]) / 0.5 > 0,
        (16.5 - start_time[1]) / 0.5 > 0
    ]
    margaret_preferences = [
        Not(day[0]),
        start_time[1] > 14.5
    ]

    # Create the solver and add the constraints
    solver = Solver()
    solver.add([day[0] + day[1] == 1])  # Exactly one day
    solver.add(margaret_monday_constraints + margaret_tuesday_constraints)
    solver.add(alexis_monday_constraints + alexis_tuesday_constraints)
    solver.add(margaret_constraints + alexis_constraints)
    solver.add(margaret_preferences)

    # Solve the problem
    if solver.check() == sat:
        model = solver.model()
        day_to_meet = 'Monday' if model[day[0]] else 'Tuesday'
        start_time_to_meet = model[start_time[0]] if day_to_meet == 'Monday' else model[start_time[1]]
        end_time_to_meet = start_time_to_meet + meeting_duration
        return f'SOLUTION:\nDay: {day_to_meet}\nStart Time: {start_time_to_meet:02d}:00\nEnd Time: {end_time_to_meet:02d}:00'
    else:
        return 'No solution found'

print(schedule_meeting())