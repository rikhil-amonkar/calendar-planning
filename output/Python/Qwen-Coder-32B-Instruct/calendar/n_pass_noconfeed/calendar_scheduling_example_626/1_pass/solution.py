from datetime import datetime, timedelta

# Define the work hours and meeting duration
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(hours=1)

# Define the busy times for each participant
patricia_busy_times = {
    "Monday": [
        (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
        (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
        (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
        (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
        (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M")),
    ],
    "Tuesday": [
        (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
        (datetime.strptime("11:00", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
        (datetime.strptime("14:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
        (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M")),
    ]
}

jesse_busy_times = {
    "Monday": [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M")),
    ],
    "Tuesday": [
        (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
        (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
        (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
        (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
        (datetime.strptime("15:30", "%H:%M"), datetime.strptime("17:00", "%H:%M")),
    ]
}

def is_time_slot_free(busy_times, start_time, end_time):
    for busy_start, busy_end in busy_times:
        if not (end_time <= busy_start or start_time >= busy_end):
            return False
    return True

def find_meeting_time(patricia_busy, jesse_busy, work_start, work_end, meeting_duration):
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        patricia_free = is_time_slot_free(patricia_busy, current_time, current_time + meeting_duration)
        jesse_free = is_time_slot_free(jesse_busy, current_time, current_time + meeting_duration)
        if patricia_free and jesse_free:
            return current_time, current_time + meeting_duration
        current_time += timedelta(minutes=30)  # Check every half hour
    return None, None

for day in ["Monday", "Tuesday"]:
    patricia_busy = patricia_busy_times[day]
    jesse_busy = jesse_busy_times[day]
    start_time, end_time = find_meeting_time(patricia_busy, jesse_busy, work_start, work_end, meeting_duration)
    if start_time and end_time:
        print(f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')} {day}")
        break