from z3 import *

def schedule_meeting(day, start_time, end_time, schedules):
    # Define the meeting duration
    meeting_duration = 30

    # Check if the meeting time conflicts with any participant's schedule
    for person, schedule in schedules.items():
        for time in schedule:
            if (start_time >= time[0] and start_time < time[1]) or \
               (end_time > time[0] and end_time <= time[1]) or \
               (start_time <= time[0] and end_time >= time[1]):
                return False

    # Check if the meeting time is within work hours
    if start_time < 9 * 60 or end_time > 17 * 60:
        return False

    # Check if the meeting duration is 30 minutes
    if end_time - start_time!= meeting_duration * 60:
        return False

    return True

def find_meeting_time(day, schedules):
    # Define the solver
    s = Solver()

    # Define the variables
    start_time = Int('start_time')
    end_time = Int('end_time')

    # Add constraints
    s.add(9 * 60 <= start_time)
    s.add(end_time <= 17 * 60)
    s.add(start_time % 30 == 0)  # Start time must be a multiple of 30 minutes
    s.add((start_time + 30) % 60 == 0)  # End time must be a multiple of 30 minutes
    s.add(end_time - start_time == 30 * 60)  # Meeting duration is 30 minutes

    # Add constraints for each participant's schedule
    for person, schedule in schedules.items():
        for time in schedule:
            s.add(Or(start_time < time[0], start_time >= time[1]))
            s.add(Or(end_time <= time[0], end_time > time[1]))

    # Check if a solution exists
    if s.check() == sat:
        # Get the solution
        model = s.model()
        start_time_val = model[start_time].as_long()
        end_time_val = model[end_time].as_long()
        return f'SOLUTION:\nDay: {day}\nStart Time: {start_time_val // 60:02d}:{start_time_val % 60:02d}\nEnd Time: {end_time_val // 60:02d}:{end_time_val % 60:02d}'
    else:
        # If no solution exists, try to find a solution by iterating over possible start times
        for hour in range(9, 17):
            for minute in range(0, 60, 30):
                start_time_val = hour * 60 + minute
                end_time_val = start_time_val + 30
                if schedule_meeting(day, start_time_val, end_time_val, schedules):
                    return f'SOLUTION:\nDay: {day}\nStart Time: {hour:02d}:{minute:02d}\nEnd Time: {hour:02d}:{minute+30:02d}'
        return 'No solution found'

# Define the schedules
schedules = {
    'Walter': [],
    'Cynthia': [(9, 9.5), (10, 10.5), (13.5, 14.5), (15, 16)],
    'Ann': [(10, 10.5), (13, 13.5), (14, 15), (16, 16.5)],
    'Catherine': [(9, 11.5), (12.5, 13.5), (14.5, 17)],
    'Kyle': [(9, 9.5), (10, 11.5), (12, 12.5), (13, 14.5), (15, 16)]
}

# Find a meeting time
print(find_meeting_time('Monday', schedules))