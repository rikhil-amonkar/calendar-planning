YOUR_CODE
from z3 import *

def schedule_meeting():
    # Define the days of the week
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']

    # Define the participants
    participants = ['Diane', 'Matthew']

    # Define the start and end times of the workday
    start_time = 9 * 60  # 9:00
    end_time = 17 * 60   # 17:00
    meeting_duration = 60  # 1 hour

    # Define the existing schedules
    diane_schedules = {
        'Monday': [12 * 60 + 0, 12 * 60 + 30, 15 * 60, 15 * 60 + 30],
        'Tuesday': [10 * 60, 11 * 60, 11 * 60 + 30, 12 * 60, 12 * 60 + 30, 16 * 60],
        'Wednesday': [9 * 60, 9 * 60 + 30, 14 * 60 + 30, 15 * 60, 16 * 60 + 30],
        'Thursday': [15 * 60 + 30, 16 * 60 + 30],
        'Friday': [9 * 60 + 30, 11 * 60 + 30, 14 * 60 + 30, 16 * 60]
    }
    matthew_schedules = {
        'Monday': [9 * 60, 10 * 60, 10 * 60 + 30, 17 * 60],
        'Tuesday': [9 * 60, 17 * 60],
        'Wednesday': [9 * 60, 11 * 60, 12 * 60, 14 * 60 + 30, 16 * 60 + 30],
        'Thursday': [9 * 60, 16 * 60],
        'Friday': [9 * 60, 17 * 60]
    }

    # Define the preferences
    matthew_preferences = {'Wednesday': 12 * 60}

    # Create a Z3 solver
    s = Solver()

    # Define the variables
    day = [Bool(f'day_{i}') for i in range(len(days))]
    start_time_var = [Int(f'start_time_{i}') for i in range(len(days))]
    end_time_var = [Int(f'end_time_{i}') for i in range(len(days))]

    # Define the constraints
    for i in range(len(days)):
        s.add(And(day[i], start_time <= start_time_var[i], start_time_var[i] + meeting_duration <= end_time_var[i], end_time_var[i] <= 17 * 60))
        for participant in participants:
            schedules = diane_schedules if participant == 'Diane' else matthew_schedules
            for schedule in schedules[days[i]]:
                s.add(Not(And(start_time_var[i] >= schedule, end_time_var[i] <= schedule)))
        if days[i] == 'Wednesday' and 'Matthew' in participants:
            s.add(start_time_var[i] >= matthew_preferences[days[i]])

    # Solve the constraints
    s.check()

    # Print the solution
    m = s.model()
    for i in range(len(days)):
        if m.evaluate(day[i]).as_bool():
            print(f'Day: {days[i]}')
            print(f'Start Time: {m.evaluate(start_time_var[i]).as_int() // 60}:{m.evaluate(start_time_var[i]).as_int() % 60:02d}')
            print(f'End Time: {m.evaluate(end_time_var[i]).as_int() // 60}:{m.evaluate(end_time_var[i]).as_int() % 60:02d}')
            print()

schedule_meeting()