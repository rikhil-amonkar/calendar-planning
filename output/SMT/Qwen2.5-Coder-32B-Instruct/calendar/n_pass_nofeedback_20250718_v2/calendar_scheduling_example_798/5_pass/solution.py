from z3 import *

# Define the variables
day = Int('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
start_time = Int('start_time')  # in minutes from 9:00

# Define the constraints
constraints = []

# Meeting duration is 30 minutes
meeting_duration = 30

# Define the work hours in minutes from 9:00
work_start = 0
work_end = 480  # 17:00 - 9:00 = 8 hours = 480 minutes

# Define the blocked times for Nancy
nancy_blocked_times = [
    (60, 90),  # 10:00 to 10:30
    (150, 210),  # 11:30 to 12:30
    (270, 300),  # 13:30 to 14:00
    (330, 390),  # 14:30 to 15:30
    (420, 480)  # 16:00 to 17:00
]

# Define the blocked times for Jose
jose_blocked_times = [
    (0, 480),  # 9:00 to 17:00 on Monday
    (0, 480),  # 9:00 to 17:00 on Tuesday
    (0, 30),  # 9:00 to 9:30 on Wednesday
    (60, 150),  # 10:00 to 12:30 on Wednesday
    (270, 290),  # 13:30 to 14:30 on Wednesday
    (360, 480)  # 15:00 to 17:00 on Wednesday
]

# Function to create available slots
def create_available_slots(blocked_times, work_start, work_end, meeting_duration):
    available_slots = []
    current_start = work_start
    for blocked_start, blocked_end in blocked_times:
        if current_start < blocked_start:
            available_slots.append((current_start, blocked_start))
        current_start = max(current_start, blocked_end)
    if current_start < work_end:
        available_slots.append((current_start, work_end))
    return available_slots

# Create available slots for Nancy and Jose
nancy_available_slots = create_available_slots(nancy_blocked_times, work_start, work_end, meeting_duration)
jose_available_slots = create_available_slots(jose_blocked_times, work_start, work_end, meeting_duration)

# Constraints for the day
constraints.append(day >= 0)
constraints.append(day <= 2)

# Constraints for the start time
constraints.append(start_time >= work_start)
constraints.append(start_time + meeting_duration <= work_end)

# Check for available slots on each day
for d in range(3):
    if d == 0:  # Monday
        constraints.append(Or(day != d, Or(
            [And(start_time >= slot[0], start_time + meeting_duration <= slot[1]) for slot in nancy_available_slots if slot[0] >= 0 and slot[1] <= 480]
        )))
    elif d == 1:  # Tuesday
        constraints.append(Or(day != d, Or(
            [And(start_time >= slot[0], start_time + meeting_duration <= slot[1]) for slot in nancy_available_slots if slot[0] >= 0 and slot[1] <= 480]
        )))
    elif d == 2:  # Wednesday
        constraints.append(Or(day != d, Or(
            [And(start_time >= slot[0], start_time + meeting_duration <= slot[1]) for slot in nancy_available_slots if slot[0] >= 0 and slot[1] <= 480]
        )))

# Check for available slots on each day for Jose
for d in range(3):
    if d == 0:  # Monday
        constraints.append(Or(day != d, Or(
            [And(start_time >= slot[0], start_time + meeting_duration <= slot[1]) for slot in jose_available_slots if slot[0] >= 0 and slot[1] <= 480]
        )))
    elif d == 1:  # Tuesday
        constraints.append(Or(day != d, Or(
            [And(start_time >= slot[0], start_time + meeting_duration <= slot[1]) for slot in jose_available_slots if slot[0] >= 0 and slot[1] <= 480]
        )))
    elif d == 2:  # Wednesday
        constraints.append(Or(day != d, Or(
            [And(start_time >= slot[0], start_time + meeting_duration <= slot[1]) for slot in jose_available_slots if slot[0] >= 0 and slot[1] <= 480]
        )))

# Solve the constraints
solver = Solver()
solver.add(constraints)

if solver.check() == sat:
    model = solver.model()
    day_value = model[day].as_long()
    start_time_value = model[start_time].as_long()
    end_time_value = start_time_value + meeting_duration

    # Convert day and time to human-readable format
    days = ["Monday", "Tuesday", "Wednesday"]
    start_time_str = f"{9 + start_time_value // 60}:{start_time_value % 60:02}"
    end_time_str = f"{9 + end_time_value // 60}:{end_time_value % 60:02}"

    print(f"SOLUTION:\nDay: {days[day_value]}\nStart Time: {start_time_str}\nEnd Time: {end_time_str}")
else:
    print("No solution found")