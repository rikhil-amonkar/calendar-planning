from datetime import datetime, timedelta

# Define the available days and time range
available_days = ["Monday", "Tuesday"]
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(minutes=30)

# Define busy times for each participant
cheryl_busy_times = {
    "Monday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
               (datetime.strptime("11:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
               (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))]
}

kyle_busy_times = {
    "Monday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                  (datetime.strptime("10:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                  (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                  (datetime.strptime("14:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

def is_time_slot_available(day, start_time, end_time, busy_times):
    for busy_start, busy_end in busy_times.get(day, []):
        if start_time < busy_end and end_time > busy_start:
            return False
    return True

def find_meeting_time():
    for day in available_days:
        current_time = work_start
        while current_time + meeting_duration <= work_end:
            next_time = current_time + meeting_duration
            if (is_time_slot_available(day, current_time, next_time, cheryl_busy_times) and
                is_time_slot_available(day, current_time, next_time, kyle_busy_times)):
                return current_time.strftime("%H:%M"), next_time.strftime("%H:%M"), day
            current_time += timedelta(minutes=15)  # Check every 15 minutes for better granularity
    return None, None, None

start_time, end_time, day = find_meeting_time()
if start_time and end_time and day:
    print(f"{start_time}:{end_time} {day}")
else:
    print("No available time slot found.")