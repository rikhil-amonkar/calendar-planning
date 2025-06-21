from z3 import *

def solve_meeting_schedule():
    # Define the variables
    day = 'Monday'
    start_time = '09:00'
    end_time = '17:00'
    meeting_duration = 30  # minutes
    participants = ['Wayne', 'Melissa', 'Catherine', 'Gregory', 'Victoria', 'Thomas', 'Jennifer']

    # Existing schedules
    schedules = {
        'Wayne': [f'{start_time}:00-{end_time}:00'],
        'Melissa': [f'10:00-11:00', f'12:30-14:00', f'15:00-15:30'],
        'Catherine': [f'{start_time}:00-{end_time}:00'],
        'Gregory': [f'12:30-13:00', f'15:30-16:00'],
        'Victoria': [f'09:00-09:30', f'10:30-11:30', f'13:00-14:00', f'14:30-15:00', f'15:30-16:30'],
        'Thomas': [f'10:00-12:00', f'12:30-13:00', f'14:30-16:00'],
        'Jennifer': [f'09:00-09:30', f'10:00-10:30', f'11:00-13:00', f'13:30-14:30', f'15:00-15:30', f'16:00-16:30']
    }

    # Wayne's preference
    wayne_preference = [f'{start_time}:00-14:00']

    # Create the solver
    s = Solver()

    # Define the meeting time variable
    meeting_time = [Bool(f'meeting_time_{i}') for i in range(8*60//meeting_duration)]  # 8 hours, 30 minutes interval

    # Define the constraints
    for participant in participants:
        for schedule in schedules[participant]:
            start_hour, start_minute = map(int, schedule.split('-')[0].split(':'))
            end_hour, end_minute = map(int, schedule.split('-')[1].split(':'))
            start_time_index = (start_hour * 60 + start_minute) // meeting_duration
            end_time_index = (end_hour * 60 + end_minute - meeting_duration) // meeting_duration
            for i in range(start_time_index, end_time_index + 1):
                s.assert_and_track(Not(meeting_time[i]), f'not_{participant}_{i}')

    # Wayne's preference
    for schedule in wayne_preference:
        start_hour, start_minute = map(int, schedule.split('-')[0].split(':'))
        end_hour, end_minute = map(int, schedule.split('-')[1].split(':'))
        start_time_index = (start_hour * 60 + start_minute) // meeting_duration
        end_time_index = (end_hour * 60 + end_minute - meeting_duration) // meeting_duration
        for i in range(start_time_index, end_time_index + 1):
            s.assert_and_track(Not(meeting_time[i]), f'not_wayne_{i}')

    # Ensure the meeting time is not empty
    s.assert_and_track(Or([meeting_time[i] for i in range(len(meeting_time))]),'meeting_time')

    # Solve the constraints
    if s.check() == sat:
        model = s.model()
        meeting_time_indices = [i for i, val in enumerate(model.eval([meeting_time[i] for i in range(len(meeting_time))], model)) if val == True]
        start_time_index = min(meeting_time_indices)
        end_time_index = max(meeting_time_indices)
        start_hour = start_time_index // 60
        start_minute = start_time_index % 60
        end_hour = end_time_index // 60
        end_minute = end_time_index % 60
        return f'SOLUTION:\nDay: {day}\nStart Time: {start_hour:02d}:{start_minute:02d}\nEnd Time: {end_hour:02d}:{end_minute:02d}'
    else:
        return 'No solution found'

print(solve_meeting_schedule())