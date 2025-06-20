YOUR_CODE
from z3 import *

def solve_scheduling_problem():
    # Define the days of the week
    days = ['Monday', 'Tuesday', 'Wednesday']

    # Define the start and end times of the work hours
    start_time = 9
    end_time = 17

    # Define the duration of the meeting
    meeting_duration = 30

    # Define the existing schedules for Ryan and Adam
    ryan_schedule = {
        'Monday': [(9, 30), (10, 0), (11, 0), (12, 0), (13, 0), (13, 30), (15, 30), (16, 0)],
        'Tuesday': [(11, 30), (15, 30), (16, 0)],
        'Wednesday': [(12, 0), (15, 30), (16, 0), (16, 30), (17, 0)]
    }

    adam_schedule = {
        'Monday': [(9, 0), (10, 30), (11, 0), (13, 30), (14, 0), (16, 0), (16, 30), (17, 0)],
        'Tuesday': [(9, 0), (10, 0), (10, 30), (16, 0), (17, 0)],
        'Wednesday': [(9, 0), (9, 30), (10, 0), (11, 0), (11, 30), (14, 30), (15, 0), (15, 30), (16, 0), (16, 30)]
    }

    # Define the preferences for Adam
    adam_preferences = {
        'Monday': [(14, 30)],
        'Tuesday': []
    }

    # Create a Z3 solver
    solver = Solver()

    # Declare the variables
    day = Int('day')
    start_hour = Int('start_hour')
    end_hour = Int('end_hour')

    # Add constraints for the day
    solver.add(day >= 0)
    solver.add(day < len(days))

    # Add constraints for the start and end times
    solver.add(start_hour >= 9)
    solver.add(start_hour <= 17)
    solver.add(end_hour >= 9)
    solver.add(end_hour <= 17)
    solver.add(end_hour > start_hour)

    # Add constraints for the meeting duration
    solver.add(end_hour - start_hour == 30)

    # Add constraints for Ryan's schedule
    for i, (start, end) in enumerate(ryan_schedule[days[day]]):
        solver.add(Or(start > end_hour, end < start_hour))

    # Add constraints for Adam's schedule
    for i, (start, end) in enumerate(adam_schedule[days[day]]):
        solver.add(Or(start > end_hour, end < start_hour))

    # Add constraints for Adam's preferences
    for i, (start, end) in enumerate(adam_preferences[days[day]]):
        solver.add(Or(start > end_hour, end < start_hour))

    # Add constraints for Ryan's preference to not meet on Wednesday
    solver.add(Or(day!= 2, start_hour!= 12))

    # Check if a solution exists
    if solver.check() == sat:
        # Get the solution
        model = solver.model()
        day = model[day].as_long()
        start_hour = model[start_hour].as_long()
        end_hour = model[end_hour].as_long()

        # Print the solution
        print('SOLUTION:')
        print(f'Day: {days[day]}')
        print(f'Start Time: {start_hour:02d}:00')
        print(f'End Time: {end_hour:02d}:00')
    else:
        print('No solution exists.')

solve_scheduling_problem()