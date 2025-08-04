from datetime import datetime, timedelta

# Define the workday start and end times
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Define the meeting duration
meeting_duration = timedelta(minutes=30)

# Define the busy times for each participant
busy_times = {
    "Christine": [
        (datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
        (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
        (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
        (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
        (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))
    ],
    "Janice": [],
    "Bobby": [
        (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
        (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M"))
    ],
    "Elizabeth": [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
        (datetime.strptime("11:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
        (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
        (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
        (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ],
    "Tyler": [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
        (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
        (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
        (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
        (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ],
    "Edward": [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
        (datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
        (datetime.strptime("11:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
        (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
        (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ]
}

# Function to check if a time slot is available for all participants
def is_time_slot_available(time_slot):
    for person, busy in busy_times.items():
        for busy_start, busy_end in busy:
            if time_slot[0] < busy_end and time_slot[1] > busy_start:
                return False
    return True

# Find a suitable time slot
current_time = work_start
while current_time + meeting_duration <= work_end:
    time_slot = (current_time, current_time + meeting_duration)
    if is_time_slot_available(time_slot) and time_slot[0].hour < 13:
        meeting_time = f"{time_slot[0].strftime('%H:%M')}:{time_slot[1].strftime('%H:%M')}"
        meeting_day = "Monday"
        break
    current_time += timedelta(minutes=30)

print(f"{meeting_time}:{meeting_day}")