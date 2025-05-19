from datetime import datetime, timedelta

# Define the working hours
working_hours_start = datetime.strptime("09:00", "%H:%M")
working_hours_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(minutes=30)

# Define the busy schedules
schedules = {
    "Monday": [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
        (datetime.strptime("11:00", "%H:%M"), datetime.strptime("16:30", "%H:%M")),
    ],
    "Tuesday": [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
        (datetime.strptime("10:00", "%H:%M"), datetime.strptime("17:00", "%H:%M")),
    ],
    "Wednesday": [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
        (datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
        (datetime.strptime("11:30", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
        (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
        (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M")),
    ],
}

# Function to check available times
def find_meeting_time():
    for day, busy_times in schedules.items():
        current_time = working_hours_start
        while current_time + meeting_duration <= working_hours_end:
            # Check if current_time is within any busy time
            if not any(start <= current_time < end for start, end in busy_times):
                # Check if current_time + meeting_duration is also not in busy times
                if not any(start <= current_time + meeting_duration <= end for start, end in busy_times):
                    return f"{day}: {current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')}"
            current_time += timedelta(minutes=15)  # Check every 15 minutes

# Get the proposed meeting time
proposed_time = find_meeting_time()
print(proposed_time)