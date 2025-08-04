from datetime import datetime, timedelta

# Define the busy times for each participant
daniel_busy = {
    'Monday': [(9, 30), (12, 0), (12, 30), (13, 0), (14, 0), (14, 30), (15, 0), (15, 30), (16, 0)],
    'Tuesday': [(11, 0), (12, 0), (13, 0), (13, 30), (15, 30), (16, 0), (16, 30), (17, 0)],
    'Wednesday': [(9, 0), (10, 0), (14, 0), (14, 30)],
    'Thursday': [(10, 30), (11, 0), (12, 0), (13, 0), (14, 30), (15, 0), (15, 30), (16, 0)],
    'Friday': [(9, 0), (9, 30), (11, 30), (12, 0), (13, 0), (13, 30), (16, 30), (17, 0)]
}

bradley_busy = {
    'Monday': [(9, 30), (11, 0), (11, 30), (12, 0), (12, 30), (13, 0), (14, 0), (14, 30), (15, 0), (15, 30), (16, 0)],
    'Tuesday': [(10, 30), (11, 0), (12, 0), (12, 30), (13, 0), (13, 30), (14, 0), (14, 30), (15, 30), (16, 0)],
    'Wednesday': [(9, 0), (10, 0), (11, 0), (12, 0), (13, 0), (13, 30), (14, 0), (14, 30), (17, 0)],
    'Thursday': [(9, 0), (10, 0), (12, 30), (13, 0), (13, 30), (14, 0), (14, 30), (15, 0), (15, 30), (16, 0)],
    'Friday': [(9, 0), (9, 30), (10, 0), (12, 0), (12, 30), (13, 0), (13, 30), (14, 0), (14, 30), (15, 0), (15, 30), (16, 0)]
}

# Meeting duration in hours and minutes
meeting_duration = timedelta(hours=0, minutes=30)

# Preferences
daniel_avoid_days = {'Wednesday', 'Thursday'}
bradley_avoid_days = {'Monday', 'Tuesday', 'Friday'}
bradley_avoid_before = 12

# Function to check if a time slot is available for both participants
def is_slot_available(day, start_time):
    end_time = start_time + meeting_duration
    if any(start_time < busy_start < end_time or start_time < busy_end < end_time for busy_start, busy_end in daniel_busy[day]):
        return False
    if any(start_time < busy_start < end_time or start_time < busy_end < end_time for busy_start, busy_end in bradley_busy[day]):
        return False
    return True

# Iterate over possible days and times to find a suitable slot
for day in ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']:
    if day in daniel_avoid_days or day in bradley_avoid_days:
        continue
    for hour in range(9, 17):
        if day == 'Tuesday' and hour < bradley_avoid_before:
            continue
        for minute in [0, 30]:
            start_time = datetime.strptime(f"{hour}:{minute}", "%H:%M")
            if is_slot_available(day, start_time):
                end_time = start_time + meeting_duration
                print(f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')} {day}")
                exit()