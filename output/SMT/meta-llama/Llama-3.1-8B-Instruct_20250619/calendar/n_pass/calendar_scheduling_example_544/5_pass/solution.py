from z3 import *

def schedule_meeting(deborah_schedule, albert_schedule, meeting_duration, day, end_time):
    # Convert meeting duration to minutes
    meeting_duration_minutes = meeting_duration * 60

    # Create Z3 solver
    s = Solver()

    # Define start time variables
    start_time = [Int(f'start_{i}') for i in range(1)]

    # Define day variable
    day_var = Int('day')

    # Define constraints
    s.add(day_var == day)
    for i in range(len(deborah_schedule)):
        s.add(Or(deborah_schedule[i], start_time[0] >= 9*60 + (i+1)*30, start_time[0] + meeting_duration_minutes <= (9*60 + (i+2)*30)))
    for i in range(len(albert_schedule)):
        s.add(Or(albert_schedule[i], start_time[0] >= 9*60 + i*60, start_time[0] + meeting_duration_minutes <= (9*60 + (i+1)*60)))
    s.add(start_time[0] >= 10*60)  # Start time must be after 10:00
    s.add(start_time[0] + meeting_duration_minutes <= end_time)

    # Solve the constraints
    if s.check() == sat:
        # Get the solution
        model = s.model()
        start_time_value = model[start_time[0]].as_long()
        # Convert start time to 24-hour format
        start_hour = start_time_value // 60
        start_minute = start_time_value % 60
        start_time_str = f'{start_hour:02d}:{start_minute:02d}'
        # Calculate end time
        end_time_value = start_time_value + meeting_duration_minutes
        end_hour = int(end_time_value // 60)
        end_minute = int(end_time_value % 60)
        end_time_str = f'{end_hour:02d}:{end_minute:02d}'
        # Print the solution
        print(f'DAY: {day}')
        print(f'START TIME: {start_time_str}')
        print(f'END TIME: {end_time_str}')
    else:
        print('No solution found')

# Existing schedules for everyone during the day
deborah_schedule = [False]*18  # Deborah is free the entire day
albert_schedule = [True, False, True, False, False, False, False, False, False, False, False, False, False, False, True, False, False]  # Albert's blocked calendar

# Meeting duration in hours
meeting_duration = 0.5

# Day to meet
day = 1  # Monday

# End time in minutes
end_time = 17*60

# Call the function
schedule_meeting(deborah_schedule, albert_schedule, meeting_duration, day, end_time)