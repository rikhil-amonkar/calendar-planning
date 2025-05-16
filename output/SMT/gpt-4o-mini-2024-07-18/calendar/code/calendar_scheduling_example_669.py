from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define working hours in minutes from midnight
work_start = 9 * 60  # 9:00 AM
work_end = 17 * 60   # 5:00 PM

# Define busy schedules for each participant
schedules = {
    'Jean': {
        'Monday': [],  # No busy times on Monday
        'Tuesday': [(11 * 60 + 30, 12 * 60), (16 * 60, 16 * 60 + 30)]  # Busy on Tuesday
    },
    'Doris': {
        'Monday': [(9 * 60, 11 * 60 + 30), (12 * 60, 12 * 60 + 30), 
                   (13 * 60 + 30, 16 * 60), (16 * 60, 17 * 60)],  # Busy on Monday
        'Tuesday': [(9 * 60, 17 * 60)]  # Busy all day on Tuesday
    }
}

# Define variables for the meeting start and end times (in minutes) and the day
day = Int('day')  # 0 for Monday, 1 for Tuesday
start_time = Int('start_time')
end_time = Int('end_time')

# Meeting duration
meeting_duration = 30  # in minutes

# Constraints to ensure meeting duration is half an hour
solver.add(end_time == start_time + meeting_duration)

# Ensure the meeting is within work hours
solver.add(start_time >= work_start)
solver.add(end_time <= work_end)

# Ensure the meeting does not overlap with any participant's busy schedules
for participant, busy_times in schedules.items():
    for day_name, busy_slots in busy_times.items():
        for busy_start, busy_end in busy_slots:
            # Add constraints for each day
            solver.add(If(day == 0, Or(start_time < busy_start, end_time > busy_end), True))  # Monday
            solver.add(If(day == 1, Or(start_time < busy_start, end_time > busy_end), True))  # Tuesday

# Additional constraints for participant preferences
solver.add(If(day == 0, start_time <= (14 * 60), True))  # Prevent Doris from meeting after 14:00 on Monday

# Constraint to allow only Monday or Tuesday
solver.add(Or(day == 0, day == 1))

# Solve the constraints
if solver.check() == sat:
    model = solver.model()

    start = model[start_time].as_long()
    end = model[end_time].as_long()
    meeting_day = model[day].as_long()

    # Convert back to standard time for output
    start_hour = start // 60
    start_minute = start % 60
    end_hour = end // 60
    end_minute = end % 60

    day_name = ["Monday", "Tuesday"][meeting_day]

    print(f"SOLUTION: Meeting on {day_name} from {start_hour:02}:{start_minute:02} to {end_hour:02}:{end_minute:02}")
else:
    print("No available time slot found.")