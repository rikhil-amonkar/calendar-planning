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
    if start_time < 9 or end_time > 17:
        return False

    # Check if the meeting duration is 30 minutes
    if end_time - start_time!= meeting_duration:
        return False

    return True

def find_meeting_time(day, schedules):
    # Define the solver
    s = Solver()

    # Define the variables
    start_hour = Int('start_hour')
    end_hour = Int('end_hour')

    # Add constraints
    s.add(9 <= start_hour)
    s.add(end_hour <= 17)
    s.add(start_hour % 1 == 0)  # Start hour must be an integer
    s.add(end_hour % 1 == 0)  # End hour must be an integer
    s.add(end_hour - start_hour == 0.5)  # Meeting duration is 30 minutes

    # Add constraints for each participant's schedule
    for person, schedule in schedules.items():
        for time in schedule:
            s.add(Or(start_hour < time[0], start_hour >= time[1]))
            s.add(Or(end_hour <= time[0], end_hour > time[1]))

    # Check if a solution exists
    if s.check() == sat:
        # Get the solution
        model = s.model()
        start_hour_val = model[start_hour].as_long()
        end_hour_val = model[end_hour].as_long()
        return f'SOLUTION:\nDay: {day}\nStart Time: {start_hour_val:02d}:00\nEnd Time: {end_hour_val:02d}:30'
    else:
        # If no solution exists, try to find a solution by iterating over possible start times
        for hour in range(9, 17):
            if schedule_meeting(day, hour * 60, (hour + 0.5) * 60, schedules):
                return f'SOLUTION:\nDay: {day}\nStart Time: {hour:02d}:00\nEnd Time: {hour+0.5:02d}:30'
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