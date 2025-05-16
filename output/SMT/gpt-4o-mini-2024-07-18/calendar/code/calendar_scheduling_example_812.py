from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define working hours in minutes from midnight
work_start = 9 * 60  # 9:00 AM
work_end = 17 * 60   # 5:00 PM

# Define existing busy schedules for Mary and Alexis
schedules = {
    'Mary': {
        'Monday': [],
        'Tuesday': [(10 * 60, 10 * 60 + 30), (15 * 60 + 30, 16 * 60)],
        'Wednesday': [(9 * 60 + 30, 10 * 60), (15 * 60, 15 * 60 + 30)],
        'Thursday': [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60 + 30)]
    },
    'Alexis': {
        'Monday': [(9 * 60, 10 * 60), (10 * 60 + 30, 12 * 60), (12 * 60 + 30, 16 * 60 + 30)],
        'Tuesday': [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60 + 30), (12 * 60, 15 * 60 + 30)],
        'Wednesday': [(9 * 60, 11 * 60), (11 * 60 + 30, 17 * 60)],
        'Thursday': [(10 * 60, 12 * 60), (14 * 60, 14 * 60 + 30), (15 * 60 + 30, 17 * 60)]
    }
}

# Define variables for the meeting start and end times (in minutes) and the day
day = Int('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday, 3 for Thursday
start_time = Int('start_time')
end_time = Int('end_time')

# Meeting duration
meeting_duration = 30  # in minutes

# Constraints to ensure meeting duration is half an hour
solver.add(end_time == start_time + meeting_duration)

# Ensure the meeting is within work hours
solver.add(start_time >= work_start)
solver.add(end_time <= work_end)

# Constraints for valid meeting days (0 = Monday, 1 = Tuesday, 2 = Wednesday, 3 = Thursday)
solver.add(Or(day == 0, day == 1, day == 2, day == 3))  # Allow meetings on all days

# Function to add busy time constraints for each schedule
def add_busy_constraints(day_key, busy_times):
    for busy_start, busy_end in busy_times[day_key]:
        solver.add(Or(start_time < busy_start, end_time > busy_end))

# Ensure the meeting does not overlap with either Mary's or Alexis's busy schedules
for day_index, day_name in enumerate(['Monday', 'Tuesday', 'Wednesday', 'Thursday']):
    solver.add(If(day == day_index, True, False))  # Ensure correct day is selected
    add_busy_constraints(day_name, schedules['Mary'])
    add_busy_constraints(day_name, schedules['Alexis'])

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

    day_name = ["Monday", "Tuesday", "Wednesday", "Thursday"][meeting_day]

    print(f"SOLUTION: Meeting on {day_name} from {start_hour:02}:{start_minute:02} to {end_hour:02}:{end_minute:02}")
else:
    print("No available time slot found.")