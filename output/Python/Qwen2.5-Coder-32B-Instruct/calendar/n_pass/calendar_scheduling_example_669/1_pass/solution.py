from datetime import datetime, timedelta

# Define the meeting duration
meeting_duration = timedelta(hours=0, minutes=30)

# Define the available time slots for Monday and Tuesday
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Jean's busy times
jean_busy_times = {
    "Tuesday": [
        (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
        (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))
    ]
}

# Doris's busy times
doris_busy_times = {
    "Monday": [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
        (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
        (datetime.strptime("13:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
        (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ],
    "Tuesday": [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ]
}

# Doris's preference not to meet after 14:00 on Monday
doris_preference_monday = datetime.strptime("14:00", "%H:%M")

def is_time_slot_free(busy_times, start_time, end_time):
    for busy_start, busy_end in busy_times:
        if start_time < busy_end and end_time > busy_start:
            return False
    return True

def find_meeting_time():
    for day in ["Monday", "Tuesday"]:
        current_time = work_start
        while current_time + meeting_duration <= work_end:
            end_time = current_time + meeting_duration
            if day == "Monday" and end_time > doris_preference_monday:
                break
            jean_busy = jean_busy_times.get(day, [])
            doris_busy = doris_busy_times.get(day, [])
            if is_time_slot_free(jean_busy, current_time, end_time) and is_time_slot_free(doris_busy, current_time, end_time):
                return current_time.strftime("%H:%M"), end_time.strftime("%H:%M"), day
            current_time += timedelta(minutes=15)  # Check every 15 minutes for availability
    return None, None, None

start_time, end_time, day = find_meeting_time()
print(f"{start_time}:{end_time} {day}")