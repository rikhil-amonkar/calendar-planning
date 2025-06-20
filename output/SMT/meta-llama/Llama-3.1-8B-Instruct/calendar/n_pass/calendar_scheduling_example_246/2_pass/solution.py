from z3 import *

# Define the day
day = 'Monday'

# Define the start and end times
start_time = 9 * 60  # 9:00 in minutes
end_time = 17 * 60  # 17:00 in minutes
duration = 30  # Meeting duration in minutes

# Define the participants and their schedules
participants = {
    'Jacob': [13 * 60 + 30, 14 * 60 + 30, 14 * 60 + 30 + 30],  # Monday 13:30, 14:00, 14:30
    'Diana': [9 * 60 + 30, 11 * 60 + 30, 13 * 60, 16 * 60],  # Monday 9:30, 11:30, 13:00, 16:00
    'Adam': [9 * 60 + 30, 11 * 60 + 30, 15 * 60 + 30],  # Monday 9:30, 11:30, 15:30
    'Angela': [9 * 60 + 30, 10 * 60 + 30, 13 * 60, 16 * 60],  # Monday 9:30, 10:30, 13:00, 16:00
    'Dennis': [9 * 60, 10 * 60 + 30, 13 * 60, 16 * 60 + 30]  # Monday 9:00, 10:30, 13:00, 16:30
}

# Create a Z3 solver
solver = Solver()

# Define the meeting time
meeting_time = [Int(f'meeting_time_{i}') for i in range(3)]

# Add constraints for each participant
for participant, schedule in participants.items():
    for i, time in enumerate(meeting_time):
        solver.add(And(time >= start_time, time <= end_time - duration))
    for time in schedule:
        for i in range(3):
            solver.add(Or(meeting_time[i]!= time, Not(And(meeting_time[0] == time, meeting_time[1] == time, meeting_time[2] == time))))

# Add constraints for the meeting duration
for i in range(3):
    solver.add(meeting_time[i] + duration <= meeting_time[(i + 1) % 3])

# Add constraints to ensure the meeting is not too early
solver.add(meeting_time[0] >= 9 * 60)

# Add constraints to ensure the meeting is not too late
solver.add(meeting_time[0] + 2 * duration <= 17 * 60)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    start_time = model[meeting_time[0]].as_long()
    end_time = model[meeting_time[0]].as_long() + duration
    print(f"SOLUTION: Day: {day}")
    print(f"Start Time: {start_time // 60:02d}:{start_time % 60:02d}")
    print(f"End Time: {(end_time // 60):02d}:{(end_time % 60):02d}")
else:
    print("No solution found")