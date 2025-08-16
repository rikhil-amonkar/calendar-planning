from datetime import datetime, timedelta

# Define the work hours and constraints
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(hours=1)

# Define the busy times for each participant
martha_busy_times = {
    "Monday": [(datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))],
    "Wednesday": [
        (datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
        (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M"))
    ]
}

beverly_busy_times = {
    "Monday": [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
        (datetime.strptime("14:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ],
    "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Wednesday": [
        (datetime.strptime("09:30", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
        (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ]
}

def is_time_slot_free(busy_times, start_time, end_time):
    for busy_start, busy_end in busy_times:
        if not (end_time <= busy_start or start_time >= busy_end):
            return False
    return True

def find_meeting_time():
    for day in ["Monday", "Tuesday", "Wednesday"]:
        current_time = work_start
        while current_time + meeting_duration <= work_end:
            martha_free = is_time_slot_free(martha_busy_times.get(day, []), current_time, current_time + meeting_duration)
            beverly_free = is_time_slot_free(beverly_busy_times.get(day, []), current_time, current_time + meeting_duration)
            if martha_free and beverly_free:
                return f"{current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')}", day
            current_time += timedelta(minutes=30)  # Check every half-hour

meeting_time, meeting_day = find_meeting_time()
print(f"{meeting_time}:{meeting_day}")