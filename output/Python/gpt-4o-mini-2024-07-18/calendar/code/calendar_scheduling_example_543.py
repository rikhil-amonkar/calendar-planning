from datetime import datetime, timedelta

# Participants' existing schedules
james_schedule = [(datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                  (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M"))]

john_schedule = [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                 (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                 (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                 (datetime.strptime("14:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]

# Meeting duration
meeting_duration = timedelta(hours=1)

# Work hours
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
date = "Monday"

# Find available slot
def find_available_slot(james_schedule, john_schedule, work_start, work_end, meeting_duration):
    # Create a list of all busy times
    busy_times = james_schedule + john_schedule
    # Add work hours as busy times if necessary
    busy_times.append((work_start, work_end))
    
    # Sort busy times
    busy_times.sort()

    # Check for available time slots
    last_end_time = work_start
    for start, end in busy_times:
        if last_end_time + meeting_duration <= start:  # Check if we have enough time before the next busy time
            return last_end_time.strftime("%H:%M"), (last_end_time + meeting_duration).strftime("%H:%M")
        last_end_time = max(last_end_time, end)

    return None  # No available slot found

time_slot = find_available_slot(james_schedule, john_schedule, work_start, work_end, meeting_duration)
if time_slot:
    print(f"{time_slot[0]}:{time_slot[1]} {date}")
else:
    print("No available time slot found.")