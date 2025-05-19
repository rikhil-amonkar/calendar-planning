from datetime import datetime, timedelta

# Define the work hours and meeting duration
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(hours=1)

# Define existing schedules
anthony_busy = [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                (datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]

pamela_busy = [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
pamela_preference_end = datetime.strptime("14:30", "%H:%M")

zachary_busy = [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                 (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                 (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                 (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
                 (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]

# Combine all busy times
busy_times = anthony_busy + pamela_busy + zachary_busy

# Function to find a free slot
def find_free_time(start, end, duration, busy_times, pamela_pref_end):
    current_time = start
    while current_time + duration <= end:
        is_free = True
        for busy_start, busy_end in busy_times:
            if busy_start < current_time + duration and current_time < busy_end:
                is_free = False
                break
        if is_free and current_time + duration <= pamela_pref_end:
            return (current_time, current_time + duration)
        current_time += timedelta(minutes=30)  # Check every 30 minutes
    return None

# Find a suitable time
free_time = find_free_time(work_start, work_end, meeting_duration, busy_times, pamela_preference_end)

if free_time:
    start_time, end_time = free_time
    print(f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')} Monday")