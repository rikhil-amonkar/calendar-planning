from datetime import datetime, timedelta

# Define the participants' busy schedules
busy_times = {
    "Christine": [("9:30", "10:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:30", "15:00"), ("16:00", "16:30")],
    "Janice": [],
    "Bobby": [("12:00", "12:30"), ("14:30", "15:00")],
    "Elizabeth": [("9:00", "9:30"), ("11:30", "13:00"), ("13:30", "14:00"), ("15:00", "15:30"), ("16:00", "17:00")],
    "Tyler": [("9:00", "11:00"), ("12:00", "12:30"), ("13:00", "13:30"), ("15:30", "16:00"), ("16:30", "17:00")],
    "Edward": [("9:00", "9:30"), ("10:00", "11:00"), ("11:30", "14:00"), ("14:30", "15:30"), ("16:00", "17:00")]
}

# Define work hours and meeting duration
work_start = datetime.strptime("9:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(minutes=30)

# Function to check if the time slot is free
def is_slot_free(start, end):
    for busy in busy_times.values():
        for busy_start, busy_end in busy:
            busy_start_dt = datetime.strptime(busy_start, "%H:%M")
            busy_end_dt = datetime.strptime(busy_end, "%H:%M")
            if not (end <= busy_start_dt or start >= busy_end_dt):
                return False
    return True

# Find a free time slot
def find_meeting_time():
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        if is_slot_free(current_time, current_time + meeting_duration):
            return current_time.strftime("%H:%M"), (current_time + meeting_duration).strftime("%H:%M"), "Monday"
        current_time += timedelta(minutes=30)  # increment in half hour intervals
    return None, None, None

start_time, end_time, day = find_meeting_time()
if start_time and end_time:
    print(f"Suggested meeting time: {{{start_time}:{end_time}}} on {day}")
else:
    print("No available meeting time.")