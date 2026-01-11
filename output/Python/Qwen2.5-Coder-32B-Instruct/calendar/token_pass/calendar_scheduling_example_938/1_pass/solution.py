from datetime import datetime, timedelta

# Define work days and hours
work_days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(minutes=30)

# Define busy times for each participant
eugene_busy = {
    "Monday": [(datetime.strptime("11:00", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
               (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
               (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
               (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                  (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                  (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                  (datetime.strptime("13:30", "%H:%M"), datetime.strptime("15:00", "%H:%M"))],
    "Thursday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                 (datetime.strptime("11:00", "%H:%M"), datetime.strptime("12:30", "%H:%M"))],
    "Friday": [(datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
               (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
               (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M"))]
}

eric_busy = {
    "Monday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                  (datetime.strptime("12:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                  (datetime.strptime("14:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Thursday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Friday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
               (datetime.strptime("11:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

def is_time_slot_available(day, start_time, busy_times):
    for busy_start, busy_end in busy_times.get(day, []):
        if busy_start <= start_time < busy_end or busy_start < start_time + meeting_duration <= busy_end:
            return False
    return True

def find_meeting_time():
    for day in work_days:
        current_time = work_start
        while current_time + meeting_duration <= work_end:
            if is_time_slot_available(day, current_time, eugene_busy) and is_time_slot_available(day, current_time, eric_busy):
                return f"{day} {current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')}"
            current_time += timedelta(minutes=30)
    return None

meeting_time = find_meeting_time()
print(meeting_time)