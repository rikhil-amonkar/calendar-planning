from z3 import *

# Define the participants and their busy times
participants = ['Jean', 'Doris']
busy_times = {
    'Jean': {
        'Monday': [],
        'Tuesday': [(11*60+30, 12*60), (16*60, 16*60+30)],
    },
    'Doris': {
        'Monday': [(9*60, 11*60+30), (12*60, 12*60+30), (13*60+30, 16*60), (16*60+30, 17*60)],
        'Tuesday': [(9*60, 17*60)],
    },
}

# Define the meeting duration
meeting_duration = 30  # in minutes

# Define the work hours
work_hours = (9*60, 17*60)  # in minutes

# Define the days of the week
days_of_week = ['Monday', 'Tuesday']

# Create a Z3 solver
s = Solver()

# Define the variables for the meeting start time and day
start_time = Int('start_time')
day = Int('day')

# Add constraints for the work hours
s.add(start_time >= work_hours[0])
s.add(start_time + meeting_duration <= work_hours[1])

# Add constraints for the days of the week
s.add(day >= 0)
s.add(day < len(days_of_week))

# Add constraints for Doris's preference
s.add(Or(day!= 0, Or(start_time < 14*60, True)))  # Monday after 14:00

# Add constraints for each participant's busy times
for participant, times in busy_times.items():
    for i, day_of_week in enumerate(days_of_week):
        for start, end in times[day_of_week]:
            s.add(Or(day!= i, Or(start_time + meeting_duration <= start, start_time >= end)))

# Check if there is a solution
if s.check() == sat:
    # Get the solution
    m = s.model()
    start_time_value = m[start_time].as_long()
    day_value = m[day].as_long()

    # Print the solution
    print(f"Day to meet: {days_of_week[day_value]}")
    print(f"Start time: {start_time_value // 60}:{start_time_value % 60:02d}")
    print(f"End time: {(start_time_value + meeting_duration) // 60}:{(start_time_value + meeting_duration) % 60:02d}")
else:
    print("No solution found.")