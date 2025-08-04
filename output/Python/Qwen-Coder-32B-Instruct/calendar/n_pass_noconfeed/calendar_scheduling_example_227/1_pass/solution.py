from datetime import datetime, timedelta

# Define the workday start and end times
workday_start = datetime.strptime("09:00", "%H:%M")
workday_end = datetime.strptime("17:00", "%H:%M")

# Define each participant's busy times
busy_times = {
    "David": [(datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
              (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M"))],
    "Douglas": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M"))],
    "Ralph": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
              (datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
              (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
              (datetime.strptime("13:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
              (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
              (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Jordan": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
               (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
               (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
               (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
               (datetime.strptime("15:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

# Meeting duration
meeting_duration = timedelta(minutes=30)

# David's preference
david_preference_start = datetime.strptime("14:00", "%H:%M")

# Function to find a suitable meeting time
def find_meeting_time(busy_times, workday_start, workday_end, meeting_duration, david_preference_start):
    current_time = david_preference_start  # Start checking from David's preferred time
    while current_time + meeting_duration <= workday_end:
        available = True
        for person, times in busy_times.items():
            for start, end in times:
                if start <= current_time < end or start < current_time + meeting_duration <= end:
                    available = False
                    break
            if not available:
                break
        if available:
            return current_time.strftime("%H:%M"), (current_time + meeting_duration).strftime("%H:%M")
        current_time += timedelta(minutes=15)  # Check every 15 minutes for availability

# Find and print the meeting time
meeting_start, meeting_end = find_meeting_time(busy_times, workday_start, workday_end, meeting_duration, david_preference_start)
print(f"{meeting_start}:{meeting_end} Monday")