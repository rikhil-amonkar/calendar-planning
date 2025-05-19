from datetime import datetime, timedelta

# Define work hours and meeting duration
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(minutes=30)

# Define existing schedules
schedules = {
    'Adam': [(datetime.strptime("14:00", "%H:%M"), datetime.strptime("15:00", "%H:%M"))],
    'John': [(datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
             (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
             (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
             (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    'Stephanie': [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                  (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                  (datetime.strptime("11:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                  (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    'Anna': [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
             (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
             (datetime.strptime("13:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
             (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

# Anna prefers not to meet before 14:30
preferred_start = datetime.strptime("14:30", "%H:%M")

# Function to check if a time range is available for all participants
def is_available(start_time, end_time):
    for schedule in schedules.values():
        for busy_start, busy_end in schedule:
            if start_time < busy_end and end_time > busy_start:
                return False
    return True

# Find a suitable time slot
current_time = max(work_start, preferred_start)
while current_time + meeting_duration <= work_end:
    if is_available(current_time, current_time + meeting_duration):
        proposed_start = current_time.strftime("%H:%M")
        proposed_end = (current_time + meeting_duration).strftime("%H:%M")
        day_of_week = "Monday"
        print(f"{proposed_start}:{proposed_end} - {day_of_week}")
        break
    current_time += timedelta(minutes=30)