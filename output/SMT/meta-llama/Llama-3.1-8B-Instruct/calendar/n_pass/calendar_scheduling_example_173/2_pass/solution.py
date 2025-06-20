from z3 import *

def schedule_meeting():
    # Define the day of the meeting
    day = 'Monday'

    # Define the start and end times of the work hours
    start_time = 9 * 60
    end_time = 17 * 60

    # Define the meeting duration
    meeting_duration = 30

    # Define the existing schedules for each participant
    jacqueline_schedule = [
        (9 * 60, 9 * 60 + 30),
        (11 * 60, 11 * 60 + 30),
        (12 * 60 + 30, 13 * 60),
        (15 * 60 + 30, 16 * 60)
    ]
    harold_schedule = [
        (10 * 60, 10 * 60 + 30),
        (13 * 60, 13 * 60 + 30),
        (15 * 60, end_time)
    ]
    arthur_schedule = [
        (9 * 60, 9 * 60 + 30),
        (10 * 60, 12 * 60 + 30),
        (14 * 60 + 30, 15 * 60),
        (15 * 60 + 30, end_time)
    ]
    kelly_schedule = [
        (9 * 60, 9 * 60 + 30),
        (10 * 60, 11 * 60),
        (11 * 60 + 30, 12 * 60 + 30),
        (14 * 60, 15 * 60),
        (15 * 60 + 30, 16 * 60)
    ]

    # Define the preferences for Harold
    harold_preference = (end_time - 1 * 60, end_time)

    # Create Z3 solver
    s = Solver()

    # Define the variables for the meeting start time
    start_time_var = Int('start_time')
    s.add(start_time_var >= start_time)
    s.add(start_time_var <= end_time - meeting_duration)

    # Check if the meeting start time conflicts with the existing schedules
    for schedule in [jacqueline_schedule, harold_schedule, arthur_schedule, kelly_schedule]:
        for start, end in schedule:
            s.add(Or(start_time_var + meeting_duration <= start, end <= start_time_var))

    # Check if the meeting start time conflicts with Harold's preference
    s.add(Or(start_time_var + meeting_duration <= harold_preference[0], harold_preference[1] <= start_time_var))

    # Check if the meeting start time is not during the time slot 13:00 to 17:00
    s.add(Or(start_time_var + meeting_duration <= 13 * 60, 17 * 60 <= start_time_var))

    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        start_time = model[start_time_var].as_long()
        end_time = start_time + meeting_duration
        print(f'SOLUTION:')
        print(f'Day: {day}')
        print(f'Start Time: {start_time // 60:02d}:{start_time % 60:02d}')
        print(f'End Time: {end_time // 60:02d}:{end_time % 60:02d}')
    else:
        print('No solution exists.')

schedule_meeting()