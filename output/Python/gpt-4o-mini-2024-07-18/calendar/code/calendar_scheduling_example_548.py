from datetime import datetime, timedelta

def find_meeting_time(start, end, duration, constraints):
    day_of_week = start.strftime("%A")
    current_time = start

    while current_time + duration <= end:
        is_available = True
        for constraint in constraints:
            if current_time < constraint[1] and (current_time + duration) > constraint[0]:
                is_available = False
                break
        
        if is_available:
            return current_time.strftime("%H:%M") + ":" + (current_time + duration).strftime("%H:%M"), day_of_week
        
        current_time += timedelta(minutes=30)  # Check every half hour

# Constraints for Judy and Nicole
judy_constraints = []
nicole_constraints = [(datetime.strptime("09:00", "%H:%M").replace(year=2023, month=10, day=2), 
                      datetime.strptime("10:00", "%H:%M").replace(year=2023, month=10, day=2)),
                     (datetime.strptime("10:30", "%H:%M").replace(year=2023, month=10, day=2), 
                      datetime.strptime("16:30", "%H:%M").replace(year=2023, month=10, day=2))]
constraints = judy_constraints + nicole_constraints

# Define working hours and meeting duration
work_start = datetime.strptime("09:00", "%H:%M").replace(year=2023, month=10, day=2)
work_end = datetime.strptime("17:00", "%H:%M").replace(year=2023, month=10, day=2)
meeting_duration = timedelta(minutes=30)

# Find a suitable meeting time
meeting_time, day = find_meeting_time(work_start, work_end, meeting_duration, constraints)
print(f"{meeting_time} on {day}")