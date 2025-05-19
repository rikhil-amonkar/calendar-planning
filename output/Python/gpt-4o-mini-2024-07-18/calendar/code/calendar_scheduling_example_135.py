from datetime import datetime, timedelta

# Participants' schedules
schedule = {
    "Eric": [],
    "Ashley": [(10, 0, 10, 30), (11, 0, 12, 0), (12, 30, 13, 0), (15, 0, 16, 0)],
    "Ronald": [(9, 0, 9, 30), (10, 0, 11, 30), (12, 30, 14, 0), (14, 30, 17, 0)],
    "Larry": [(9, 0, 12, 0), (13, 0, 17, 0)]
}

# Meeting duration
meeting_duration = timedelta(minutes=30)

# Work hours
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Function to check if a time slot is free
def is_free(start, end):
    for times in schedule.values():
        for t in times:
            booked_start = datetime(*t[:2])
            booked_end = datetime(*t[2:])
            if (start < booked_end and end > booked_start):
                return False
    return True

# Finding a suitable time
current_time = work_start
while current_time + meeting_duration <= work_end:
    next_time = current_time + meeting_duration
    if is_free(current_time, next_time):
        print(f"Suggested meeting time: {current_time.strftime('%H:%M')} to {next_time.strftime('%H:%M')} on Monday")
        break
    current_time += timedelta(minutes=30)