from datetime import datetime, timedelta

# Define the work hours
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Define the meeting duration
meeting_duration = timedelta(hours=1)

# Define the busy times for each participant
betty_busy_times = {
    "Monday": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
               (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
               (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                (datetime.strptime("13:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
                (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Wednesday": [(datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                  (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M"))],
    "Friday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
               (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
               (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
               (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M"))]
}

megan_busy_times = {
    "Monday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                (datetime.strptime("12:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                  (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                  (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                  (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                  (datetime.strptime("15:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Thursday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                 (datetime.strptime("11:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                 (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
                 (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Friday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

# Function to check if a time slot is free for both participants
def is_time_slot_free(day, start_time, end_time):
    for busy_start, busy_end in betty_busy_times.get(day, []):
        if not (end_time <= busy_start or start_time >= busy_end):
            return False
    for busy_start, busy_end in megan_busy_times.get(day, []):
        if not (end_time <= busy_start or start_time >= busy_end):
            return False
    return True

# Find a suitable time slot
for day in ["Monday", "Tuesday", "Friday"]:
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        if is_time_slot_free(day, current_time, current_time + meeting_duration):
            print(f"{current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')} {day}")
            break
        current_time += timedelta(minutes=30)