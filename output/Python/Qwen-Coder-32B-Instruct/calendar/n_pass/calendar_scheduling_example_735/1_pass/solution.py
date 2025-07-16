from datetime import datetime, timedelta

# Define the work hours
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Define the meeting duration
meeting_duration = timedelta(minutes=30)

# Define the schedules for Ronald and Amber
ronald_schedule = {
    "Monday": [(datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
               (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
               (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                  (datetime.strptime("11:00", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                  (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                  (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                  (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

amber_schedule = {
    "Monday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
               (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
               (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
               (datetime.strptime("12:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
               (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
               (datetime.strptime("15:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                (datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                (datetime.strptime("13:30", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                  (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                  (datetime.strptime("11:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                  (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))]
}

# Function to find the first available slot
def find_available_slot(day):
    current_time = work_start
    while current_time < work_end - meeting_duration:
        available = True
        for schedule in [ronald_schedule[day], amber_schedule[day]]:
            for start, end in schedule:
                if start <= current_time < end or start < current_time + meeting_duration <= end:
                    available = False
                    break
            if not available:
                break
        if available:
            return current_time.strftime("%H:%M"), (current_time + meeting_duration).strftime("%H:%M")
        current_time += timedelta(minutes=15)  # Check every 15 minutes for better granularity
    return None, None

# Find the earliest available slot
for day in ["Monday", "Tuesday", "Wednesday"]:
    start_time, end_time = find_available_slot(day)
    if start_time and end_time:
        print(f"{start_time}:{end_time} {day}")
        break