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

# Define the unavailable time slots
unavailable_time_slots = [
    (start_time, start_time + 30),  # 9:00 to 9:30
    (start_time + 11 * 60, start_time + 11 * 60 + 30),  # 11:00 to 11:30
    (start_time + 14 * 60, start_time + 14 * 60 + 30),  # 14:30 to 15:00
    (start_time + 9 * 60, start_time + 10 * 60),  # 9:30 to 10:00
    (start_time + 10 * 60, start_time + 12 * 60),  # 10:00 to 12:00
    (start_time + 12 * 60, start_time + 12 * 60 + 30),  # 12:00 to 12:30
    (start_time + 14 * 60, start_time + 17 * 60),  # 14:00 to 17:00
    (start_time, start_time + 9 * 60 + 30),  # 9:00 to 10:30
    (start_time + 11 * 60 + 30, start_time + 12 * 60 + 30),  # 11:30 to 12:00
    (start_time + 13 * 60, start_time + 14 * 60),  # 13:00 to 14:00
    (start_time + 14 * 60 + 30, start_time + 15 * 60 + 30),  # 14:30 to 15:30
    (start_time + 16 * 60, start_time + 17 * 60),  # 16:00 to 17:00
    (start_time + 10 * 60, start_time + 12 * 60),  # 10:30 to 12:00
    (start_time + 12 * 60 + 30, start_time + 13 * 60 + 30),  # 12:30 to 13:00
    (start_time + 13 * 60 + 30, start_time + 14 * 60 + 30),  # 13:00 to 14:00
    (start_time + 16 * 60 + 30, start_time + 16 * 60 + 30 + 30),  # 16:30 to 17:00
]

# Define the solver
solver = Solver()

# Define the variables
time = Int('time')
time_range = [start_time + i for i in range((end_time - start_time) // 30 + 1)]

# Add constraints for each unavailable time slot
for start, end in unavailable_time_slots:
    solver.add(And(time >= start, time <= end))

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