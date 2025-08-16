from datetime import datetime, timedelta

# Define work hours and meeting duration
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(hours=1)

# Define participants' busy times
busy_times = {
    "Monday": [
        (datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
        (datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
        (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
        (datetime.strptime("15:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ],
    "Tuesday": [
        (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
        (datetime.strptime("12:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
        (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
        (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ],
    "Wednesday": [
        (datetime.strptime("09:30", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
        (datetime.strptime("12:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
        (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
        (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ]
}

# Function to check if a time slot is free
def is_free(time_slot, busy_times):
    start, end = time_slot
    for busy_start, busy_end in busy_times:
        if not (end <= busy_start or start >= busy_end):
            return False
    return True

# Find available time slot
for day, day_busy_times in busy_times.items():
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        time_slot = (current_time, current_time + meeting_duration)
        if is_free(time_slot, day_busy_times):
            print(f"{current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')} {day}")
            break
        current_time += timedelta(minutes=30)
    else:
        continue
    break