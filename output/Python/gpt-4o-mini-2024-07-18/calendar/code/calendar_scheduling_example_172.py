from datetime import datetime, timedelta

# Participants' schedules
schedules = {
    "Patrick": [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
        (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
        (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
        (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M")),
    ],
    "Kayla": [
        (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
        (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
        (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M")),
    ],
    "Carl": [
        (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
        (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
        (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
        (datetime.strptime("14:30", "%H:%M"), datetime.strptime("17:00", "%H:%M")),
    ],
    "Christian": [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
        (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
        (datetime.strptime("14:30", "%H:%M"), datetime.strptime("17:00", "%H:%M")),
    ]
}

# Meeting duration
meeting_duration = timedelta(minutes=30)

# Work hours
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Function to find available time
def find_meeting_time(schedules, duration):
    # Create a list of busy times
    busy_times = []
    for times in schedules.values():
        busy_times.extend(times)

    # Sort busy times
    busy_times.sort(key=lambda x: x[0])

    # Find free slots
    last_end_time = work_start

    for start, end in busy_times:
        if last_end_time + duration <= start:
            return last_end_time.strftime("%H:%M"), (last_end_time + duration).strftime("%H:%M")
        
        last_end_time = max(last_end_time, end)

    if last_end_time + duration <= work_end:
        return last_end_time.strftime("%H:%M"), (last_end_time + duration).strftime("%H:%M")

    return None

# Find the meeting time
result = find_meeting_time(schedules, meeting_duration)

# Output the result
if result:
    start_time, end_time = result
    print(f"Meeting Time: {{{start_time}:{end_time}}}, Day: Monday")