from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define working hours in minutes from midnight
work_start = 9 * 60  # 9:00 AM
work_end = 17 * 60   # 5:00 PM

# Define busy schedules for each participant
schedules = {
    'Brian': {
        'Monday': [(9 * 60 + 30, 10 * 60), (12 * 60 + 30, 14 * 60), 
                   (15 * 60 + 30, 16 * 60)],
        'Tuesday': [(9 * 60, 9 * 60 + 30)],
        'Wednesday': [(12 * 60 + 30, 14 * 60), (16 * 60 + 30, 17 * 60)],
        'Thursday': [(11 * 60, 11 * 60 + 30), (13 * 60, 13 * 60 + 30), 
                     (16 * 60 + 30, 17 * 60)],
        'Friday': [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 11 * 60), 
                   (13 * 60, 13 * 60 + 30), (15 * 60, 16 * 60), 
                   (16 * 60 + 30, 17 * 60)],
    },
    'Julia': {
        'Monday': [(9 * 60, 10 * 60), (11 * 60, 11 * 60 + 30), 
                   (12 * 60 + 30, 13 * 60), (15 * 60 + 30, 16 * 60)],
        'Tuesday': [(13 * 60, 14 * 60), (16 * 60, 16 * 60 + 30)],
        'Wednesday': [(9 * 60, 11 * 60 + 30), (12 * 60, 12 * 60 + 30), 
                      (13 * 60, 17 * 60)],
        'Thursday': [(9 * 60, 10 * 60 + 30), (11 * 60, 17 * 60)],
        'Friday': [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60 + 30), 
                   (12 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60), 
                   (15 * 60 + 30, 16 * 60)],
    }
}

# Define variables for the meeting start and end times (in minutes) and for the day
day = Int('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday, 3 for Thursday, 4 for Friday
start_time = Int('start_time')
end_time = Int('end_time')

# Meeting duration
meeting_duration = 60  # in minutes

# Constraints to ensure the meeting duration is one hour
solver.add(end_time == start_time + meeting_duration)

# Ensure the meeting is within working hours
solver.add(start_time >= work_start)
solver.add(end_time <= work_end)

# Ensure the meeting does not overlap with any participant's busy schedules
for participant, busy_times in schedules.items():
    for day_name, busy_slots in busy_times.items():
        for busy_start, busy_end in busy_slots:
            # Add constraints for each day
            solver.add(If(day == 0, Or(start_time < busy_start, end_time > busy_end), True))  # Monday
            solver.add(If(day == 1, Or(start_time < busy_start, end_time > busy_end), True))  # Tuesday
            solver.add(If(day == 2, Or(start_time < busy_start, end_time > busy_end), True))  # Wednesday
            solver.add(If(day == 3, Or(start_time < busy_start, end_time > busy_end), True))  # Thursday
            solver.add(If(day == 4, Or(start_time < busy_start, end_time > busy_end), True))  # Friday

# Additional constraint: Brian would like to avoid more meetings on Monday
solver.add(start_time >= 13 * 60)  # Meetings for Brian on Monday should start after 1 PM

# Solve the constraints
solver.add(Or(day == 0, day == 1, day == 2, day == 3, day == 4))  # Allow meeting on available days

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

    day_name = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"][meeting_day]

    print(f"SOLUTION: Meeting on {day_name} from {start_hour:02}:{start_minute:02} to {end_hour:02}:{end_minute:02}")
else:
    print("No available time slot found.")