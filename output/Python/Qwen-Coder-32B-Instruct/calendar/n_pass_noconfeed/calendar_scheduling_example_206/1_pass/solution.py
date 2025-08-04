from datetime import datetime, timedelta

# Define the work hours
start_time = datetime.strptime("09:00", "%H:%M")
end_time = datetime.strptime("17:00", "%H:%M")

# Define the meeting duration
meeting_duration = timedelta(minutes=30)

# Define the busy times for each participant
busy_times = {
    "Shirley": [datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M"),
                datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")],
    "Jacob": [datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M"),
              datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M"),
              datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M"),
              datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:30", "%H:%M"),
              datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")],
    "Stephen": [datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M"),
                datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")],
    "Margaret": [datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M"),
                 datetime.strptime("10:30", "%H:%M"), datetime.strptime("12:30", "%H:%M"),
                 datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M"),
                 datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"),
                 datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M")],
    "Mason": [datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M"),
              datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M"),
              datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:30", "%H:%M"),
              datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M"),
              datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M"),
              datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M")]
}

# Margaret's preference
margaret_preference_start = datetime.strptime("14:30", "%H:%M")

# Function to check if a time slot is free for all participants
def is_free_for_all(start):
    end = start + meeting_duration
    for person, times in busy_times.items():
        for i in range(0, len(times), 2):
            if start < times[i+1] and end > times[i]:
                return False
    return True

# Find a suitable time slot
current_time = margaret_preference_start
while current_time + meeting_duration <= end_time:
    if is_free_for_all(current_time):
        meeting_start = current_time.strftime("%H:%M")
        meeting_end = (current_time + meeting_duration).strftime("%H:%M")
        print(f"{meeting_start}:{meeting_end} Monday")
        break
    current_time += timedelta(minutes=15)