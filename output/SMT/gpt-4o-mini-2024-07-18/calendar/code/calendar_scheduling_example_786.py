from z3 import *

# Create a Z3 solver instance
solver = Solver()

# Define work hours in minutes from midnight
work_start = 9 * 60  # 9:00 AM
work_end = 17 * 60   # 5:00 PM

# Define existing busy schedules for Amy and Pamela
schedules = {
    'Amy': {
        'Monday': [],
        'Tuesday': [],
        'Wednesday': [(11 * 60, 11 * 60 + 30), (13 * 60 + 30, 14 * 60)]  # Busy on Wednesday
    },
    'Pamela': {
        'Monday': [(9 * 60, 10 * 60 + 30), (11 * 60, 16 * 60)],  # Busy on Monday
        'Tuesday': [(9 * 60, 9 * 60 + 30), (10 * 60, 17 * 60)],  # Busy on Tuesday
        'Wednesday': [
            (9 * 60, 9 * 60 + 30), 
            (10 * 60, 11 * 60), 
            (11 * 60 + 30, 13 * 60 + 30), 
            (14 * 60 + 30, 15 * 60), 
            (16 * 60, 16 * 60 + 30)
        ]  # Busy on Wednesday
    }
}

# Define variables for the meeting start and end times (in minutes) and the day
day = Int('day')  # 0 for Monday, 1 for Tuesday, 2 for Wednesday
start_time = Int('start_time')
end_time = Int('end_time')

# Meeting duration
meeting_duration = 30  # in minutes

# Constraints to ensure meeting duration is half an hour
solver.add(end_time == start_time + meeting_duration)

# Ensure the meeting is within work hours
solver.add(start_time >= work_start)
solver.add(end_time <= work_end)

# Constraints for valid meeting days (0 = Monday, 1 = Tuesday, 2 = Wednesday)
solver.add(Or(day == 0, day == 1, day == 2))

# Function to add busy time constraints for each schedule
def add_busy_constraints(day_key, busy_times):
    for busy_start, busy_end in busy_times[day_key]:
        solver.add(Or(start_time < busy_start, end_time > busy_end))

# Ensure the meeting does not overlap with either Amy's or Pamela's busy schedules
for day_index, day_name in enumerate(['Monday', 'Tuesday', 'Wednesday']):
    # Add busy constraints for each day
    scheduler_for_day = If(day == day_index, True, False)
    solver.add(scheduler_for_day)
    
    add_busy_constraints(day_name, schedules['Amy'])
    add_busy_constraints(day_name, schedules['Pamela'])

# Additional constraints based on Pamela's preferences
solver.add(If(day == 0, start_time > (16 * 60), True))  # Avoid meetings on Monday after 16:00
solver.add(If(day == 1, start_time > (16 * 60), True))  # Avoid meetings on Tuesday after 16:00
solver.add(If(day == 2, start_time >= (16 * 60), True))  # Avoid meetings on Wednesday before 16:00

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
    
    day_name = ["Monday", "Tuesday", "Wednesday"][meeting_day]
    
    print(f"SOLUTION: Meeting on {day_name} from {start_hour:02}:{start_minute:02} to {end_hour:02}:{end_minute:02}")
else:
    print("No available time slot found.")