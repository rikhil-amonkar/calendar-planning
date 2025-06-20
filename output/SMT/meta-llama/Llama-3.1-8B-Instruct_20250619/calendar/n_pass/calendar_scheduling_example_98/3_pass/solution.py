from z3 import *

def schedule_meeting():
    # Define the day
    day = 'Monday'

    # Define the start and end time of work hours
    start_time = 9 * 60
    end_time = 17 * 60

    # Define the meeting duration
    meeting_duration = 30

    # Define the existing schedules for each participant
    juan_schedules = [9 * 60, 10 * 30], [15 * 60, 16 * 60]
    marilyn_schedules = [11 * 60, 11 * 60 + 30], [12 * 60 + 30, 13 * 60]
    ronald_schedules = [9 * 60, 10 * 30], [12 * 60, 12 * 60 + 30], [13 * 60, 13 * 60 + 30], [14 * 60, 16 * 60 + 30]

    # Define the variables for the start time of the meeting
    start_time_var = Int('start_time')

    # Define the constraints for the start time of the meeting
    constraints = [
        And(start_time_var >= 9 * 60, start_time_var <= 16 * 60),
        start_time_var + meeting_duration <= 16 * 60,  # Juan can not meet on Monday after 16:00
        start_time_var + meeting_duration <= 16 * 60
    ]

    # Add constraints for each participant's schedule
    for schedule in juan_schedules + marilyn_schedules + ronald_schedules:
        constraints.append(Or(start_time_var + meeting_duration <= schedule[0], start_time_var >= schedule[1]))

    # Solve the constraints
    solver = Solver()
    solver.add(constraints)
    if solver.check() == sat:
        model = solver.model()
        start_time_value = model[start_time_var].as_long()
        end_time_value = start_time_value + meeting_duration
        print(f'SOLUTION:')
        print(f'Day: {day}')
        print(f'Start Time: {start_time_value // 60:02d}:{start_time_value % 60:02d}')
        print(f'End Time: {end_time_value // 60:02d}:{end_time_value % 60:02d}')
    else:
        print('No solution found')

schedule_meeting()