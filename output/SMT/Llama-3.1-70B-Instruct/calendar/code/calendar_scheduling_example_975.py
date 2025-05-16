from z3 import *

# Define the participants and their busy times
participants = ['Nicole', 'Daniel']
busy_times = {
    'Nicole': {
        'Monday': [],
        'Tuesday': [(16*60, 16*60+30)],
        'Wednesday': [(15*60, 15*60+30)],
        'Thursday': [],
        'Friday': [(12*60, 12*60+30), (15*60+30, 16*60)],
    },
    'Daniel': {
        'Monday': [(9*60, 12*60+30), (13*60, 13*60+30), (14*60, 16*60+30)],
        'Tuesday': [(9*60, 10*60+30), (11*60+30, 12*60+30), (13*60, 13*60+30), (15*60, 16*60), (16*60+30, 17*60)],
        'Wednesday': [(9*60, 10*60), (11*60, 12*60+30), (13*60, 13*60+30), (14*60, 14*60+30), (16*60+30, 17*60)],
        'Thursday': [(11*60, 12*60), (13*60, 14*60), (15*60, 15*60+30)],
        'Friday': [(10*60, 11*60), (11*60+30, 12*60), (12*60+30, 14*60+30), (15*60, 15*60+30), (16*60, 16*60+30)],
    },
}

# Define the meeting duration
meeting_duration = 60  # in minutes

# Define the work hours
work_hours = (9*60, 17*60)  # in minutes

# Define the days of the week
days_of_week = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']

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

# Add constraints for each participant's busy times
for participant, times in busy_times.items():
    for i, day_of_week in enumerate(days_of_week):
        for start, end in times[day_of_week]:
            s.add(Or(day!= i, Or(start_time + meeting_duration <= start, start_time >= end)))

# Add a constraint to meet at the earliest availability
s.add(ForAll([day, start_time], Implies(And(0 <= day, day < len(days_of_week), work_hours[0] <= start_time, start_time + meeting_duration <= work_hours[1]), 
    Or(day == 0, day == 1, day == 2, day == 3, day == 4))))

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