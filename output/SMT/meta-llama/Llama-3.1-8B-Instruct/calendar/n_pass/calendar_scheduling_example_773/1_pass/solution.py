from z3 import *

def solve_scheduling_problem():
    # Define the days of the week
    days = ['Monday', 'Tuesday', 'Wednesday']

    # Define the start and end times
    start_times = [9, 10, 11, 12, 13, 14, 15, 16]
    end_times = [17]

    # Define the meeting duration
    meeting_duration = 1

    # Define the existing schedules for Roy
    roy_schedules = {
        'Monday': [
            (10, 11.5), (12, 13), (14, 14.5), (15, 17)
        ],
        'Tuesday': [
            (10.5, 11.5), (12, 14.5), (15, 15.5), (16, 17)
        ],
        'Wednesday': [
            (9.5, 11.5), (12.5, 14), (14.5, 15.5), (16.5, 17)
        ]
    }

    # Define the solver
    s = Solver()

    # Define the variables
    day = Int('day')
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Add constraints for the day
    s.add(day >= 0)
    s.add(day < len(days))

    # Add constraints for the start and end times
    s.add(start_time >= 9)
    s.add(start_time < 17)
    s.add(end_time == start_time + meeting_duration)

    # Add constraints for the existing schedules of Roy
    for d in range(len(days)):
        for t in roy_schedules[days[d]]:
            s.add(Or(start_time + t[0] > end_time, start_time + t[1] < start_time))

    # Check if a solution exists
    s.check()

    # Get the solution
    m = s.model()

    # Print the solution
    print('SOLUTION:')
    print(f'Day: {days[m[day].as_long()]}')
    print(f'Start Time: {m[start_time].as_long():02d}:00')
    print(f'End Time: {m[end_time].as_long():02d}:00')

# Run the solver
solve_scheduling_problem()