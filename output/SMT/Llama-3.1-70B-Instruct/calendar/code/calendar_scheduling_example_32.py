from z3 import *

# Define the participants and their busy times
participants = ['Emily', 'Melissa', 'Frank']
busy_times = {
    'Emily': [(10*60, 10*60+30), (11*60+30, 12*60+30), (14*60, 15*60), (16*60, 16*60+30)],
    'Melissa': [(9*60+30, 10*60), (14*60+30, 15*60)],
    'Frank': [(10*60, 10*60+30), (11*60, 11*60+30), (12*60+30, 13*60), (13*60+30, 14*60+30), (15*60, 16*60), (16*60+30, 17*60)],
}

# Define the meeting duration
meeting_duration = 30  # in minutes

# Define the work hours
work_hours = (9*60, 17*60)  # in minutes

# Create a Z3 solver
s = Solver()

# Define the variables for the meeting start time
start_time = Int('start_time')

# Add constraints for the work hours
s.add(start_time >= work_hours[0])
s.add(start_time + meeting_duration <= work_hours[1])

# Add constraints for Frank's preference
s.add(start_time < 9*60 + 30)

# Add constraints for each participant's busy times
for participant, times in busy_times.items():
    for start, end in times:
        s.add(Or(start_time + meeting_duration <= start, start_time >= end))

# Check if there is a solution
if s.check() == sat:
    # Get the solution
    m = s.model()
    start_time_value = m[start_time].as_long()

    # Print the solution
    print(f"Day to meet: Monday")
    print(f"Start time: {start_time_value // 60}:{start_time_value % 60:02d}")
    print(f"End time: {(start_time_value + meeting_duration) // 60}:{(start_time_value + meeting_duration) % 60:02d}")
else:
    print("No solution found.")