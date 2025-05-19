from datetime import datetime, timedelta

# Define the schedules
margaret_schedule = {
    "Monday": [
        ("10:30", "11:00"),
        ("11:30", "12:00"),
        ("13:00", "13:30"),
        ("15:00", "17:00"),
    ],
    "Tuesday": [
        ("12:00", "12:30"),
    ]
}

alexis_schedule = {
    "Monday": [
        ("09:30", "11:30"),
        ("12:30", "13:00"),
        ("14:00", "17:00"),
    ],
    "Tuesday": [
        ("09:00", "09:30"),
        ("10:00", "10:30"),
        ("14:00", "16:30"),
    ]
}

# Meeting constraints
meeting_duration = timedelta(minutes=30)
margaret_preference_day = "Tuesday"
margaret_preference_time_start = "14:30"

# Define work hours
work_hours_start = "09:00"
work_hours_end = "17:00"

# Function to convert time strings to datetime objects
def convert_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

# Function to check availability
def is_time_available(schedule, day, meeting_start, meeting_end):
    for start, end in schedule.get(day, []):
        if not (meeting_end <= convert_time(start) or meeting_start >= convert_time(end)):
            return False
    return True

# Check availability for Tuesday after 14:30
day = margaret_preference_day
start_time = convert_time(margaret_preference_time_start)
end_time = convert_time(work_hours_end)

# Find suitable time slot
current_time = start_time
while current_time + meeting_duration <= end_time:
    meeting_start = current_time
    meeting_end = meeting_start + meeting_duration

    if is_time_available(margaret_schedule, day, meeting_start, meeting_end) and \
       is_time_available(alexis_schedule, day, meeting_start, meeting_end):
        print(f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}")
        print(day)
        break

    current_time += timedelta(minutes=30)  # Increment to next half hour