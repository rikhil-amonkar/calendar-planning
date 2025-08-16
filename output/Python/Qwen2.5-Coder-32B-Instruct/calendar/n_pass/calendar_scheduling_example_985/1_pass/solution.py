from datetime import datetime, timedelta

# Define the work hours
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Define the busy times for Diane and Matthew
diane_busy_times = {
    "Monday": [(datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
               (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))],
    "Tuesday": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                  (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
                  (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Thursday": [(datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Friday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
               (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
               (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

matthew_busy_times = {
    "Monday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
               (datetime.strptime("10:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                  (datetime.strptime("12:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                  (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Thursday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
    "Friday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

# Meeting duration
meeting_duration = timedelta(hours=1)

# Preference for Matthew
matthew_preference = {"Wednesday": datetime.strptime("12:30", "%H:%M")}

# Function to check if a time slot is free for both participants
def is_slot_free(day, start_time):
    end_time = start_time + meeting_duration
    if any(start_time < busy_end and end_time > busy_start for busy_start, busy_end in diane_busy_times[day]):
        return False
    if any(start_time < busy_end and end_time > busy_start for busy_start, busy_end in matthew_busy_times[day]):
        return False
    if day == "Wednesday" and start_time < matthew_preference["Wednesday"]:
        return False
    return True

# Find a suitable time slot
for day in ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]:
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        if is_slot_free(day, current_time):
            print(f"{current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')} {day}")
            break
        current_time += timedelta(minutes=30)