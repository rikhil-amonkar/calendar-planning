from z3 import *

# Define the day
day = 'Monday'

# Define the start and end times
start_time = 9 * 60  # 9:00
end_time = 17 * 60  # 17:00
meeting_duration = 30  # 30 minutes

# Define the participants and their schedules
participants = {
    'Tyler': [start_time, end_time],
    'Kelly': [start_time, end_time],
    'Stephanie': [start_time + 11 * 60, start_time + 11 * 60 + 30],
    'Hannah': [start_time, end_time],
    'Joe': [start_time, start_time + 9 * 60, start_time + 10 * 60, start_time + 12 * 60, start_time + 12 * 60 + 30, start_time + 14 * 60, start_time + 17 * 60],
    'Diana': [start_time, start_time + 9 * 60 + 30, start_time + 11 * 60 + 30, start_time + 12 * 60 + 30, start_time + 14 * 60 + 30, start_time + 16 * 60],
    'Deborah': [start_time, start_time + 10 * 60, start_time + 12 * 60, start_time + 12 * 60 + 30, start_time + 13 * 60 + 30, start_time + 14 * 60 + 30, start_time + 16 * 60 + 30]
}

# Define the solver
solver = Solver()

# Define the variables
time = Int('time')
time_range = [start_time + i for i in range((end_time - start_time) // 30 + 1)]

# Add constraints for each participant
for participant, schedule in participants.items():
    for block in schedule:
        if block < start_time or block + 30 > end_time:
            continue
        solver.add(And(time >= block, time <= block + 30))

# Add constraint for meeting duration
solver.add(And(time >= start_time, time + meeting_duration <= end_time))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    time_value = model[time].as_long()
    print(f"SOLUTION:")
    print(f"Day: {day}")
    print(f"Start Time: {time_value // 60:02d}:{time_value % 60:02d}")
    print(f"End Time: {(time_value // 60 + meeting_duration // 60):02d}:{(time_value % 60 + meeting_duration % 60):02d}")
else:
    print("No solution found.")