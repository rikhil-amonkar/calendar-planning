from datetime import datetime, timedelta

# Define participant schedules
schedules = {
    "Kimberly": [("10:00", "10:30"), ("11:00", "12:00"), ("16:00", "16:30")],
    "Megan": [],
    "Marie": [("10:00", "11:00"), ("11:30", "15:00"), ("16:00", "16:30")],
    "Diana": [("09:30", "10:00"), ("10:30", "14:30"), ("15:30", "17:00")]
}

# Meeting parameters
meeting_duration = timedelta(minutes=30)
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
day_of_week = "Monday"

# Function to check availability
def is_available(start_time, end_time):
    for busy_periods in schedules.values():
        for start, end in busy_periods:
            busy_start = datetime.strptime(start, "%H:%M")
            busy_end = datetime.strptime(end, "%H:%M")
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
    return True

# Loop through possible time slots
current_time = work_start
while current_time + meeting_duration <= work_end:
    end_time = current_time + meeting_duration
    if is_available(current_time, end_time):
        print(f"{current_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}")
        print(day_of_week)
        break
    current_time += timedelta(minutes=30)