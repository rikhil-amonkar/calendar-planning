from datetime import datetime, timedelta

# Define the workday start and end times
workday_start = datetime.strptime("09:00", "%H:%M")
workday_end = datetime.strptime("17:00", "%H:%M")

# Define the meeting duration
meeting_duration = timedelta(minutes=30)

# Define the busy times for each participant
busy_times = {
    "Gregory": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M"))],
    "Jonathan": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                 (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                 (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                 (datetime.strptime("15:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                 (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Barbara": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M"))],
    "Jesse": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
              (datetime.strptime("12:30", "%H:%M"), datetime.strptime("14:30", "%H:%M"))],
    "Alan": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
             (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
             (datetime.strptime("13:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
             (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Nicole": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
               (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
               (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
               (datetime.strptime("14:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Catherine": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                  (datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                  (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                  (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]
}

# Function to check if a time slot is available for all participants
def is_slot_available(start_time, busy_times):
    for person, times in busy_times.items():
        for busy_start, busy_end in times:
            if busy_start <= start_time < busy_end or busy_start < start_time + meeting_duration <= busy_end:
                return False
    return True

# Find a suitable time slot
current_time = workday_start
while current_time + meeting_duration <= workday_end:
    if is_slot_available(current_time, busy_times):
        meeting_start = current_time.strftime("%H:%M")
        meeting_end = (current_time + meeting_duration).strftime("%H:%M")
        print(f"{meeting_start}:{meeting_end} Monday")
        break
    current_time += timedelta(minutes=30)