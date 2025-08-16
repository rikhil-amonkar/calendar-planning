from datetime import datetime, timedelta

# Define the workday start and end times
workday_start = datetime.strptime("09:00", "%H:%M")
workday_end = datetime.strptime("17:00", "%H:%M")

# Define the busy times for each participant
busy_times = {
    "Stephanie": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                  (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Cheryl": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                 (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                 (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                 (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Bradley": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                  (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                  (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                  (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
                  (datetime.strptime("15:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Steven": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                 (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                 (datetime.strptime("14:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

# Function to check if a time slot is available for all participants
def is_time_slot_available(start_time, duration):
    end_time = start_time + timedelta(hours=duration)
    for person, times in busy_times.items():
        for busy_start, busy_end in times:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
    return True

# Find a suitable time slot
meeting_duration = 1  # Meeting duration in hours
current_time = workday_start

while current_time + timedelta(hours=meeting_duration) <= workday_end:
    if is_time_slot_available(current_time, meeting_duration):
        meeting_start = current_time.strftime("%H:%M")
        meeting_end = (current_time + timedelta(hours=meeting_duration)).strftime("%H:%M")
        print(f"{meeting_start}:{meeting_end} Monday")
        break
    current_time += timedelta(minutes=30)  # Check every 30 minutes