from datetime import datetime, timedelta

# Define the meeting duration and participants' schedules
meeting_duration = timedelta(hours=1)
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Participant schedules (start and end times of blocked periods)
olivia_schedule = [(datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                   (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
                   (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]

virginia_schedule = [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                     (datetime.strptime("11:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                     (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]

paul_schedule = [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                 (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                 (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                 (datetime.strptime("14:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                 (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]

# Combine all blocked schedules
blocked_times = olivia_schedule + virginia_schedule + paul_schedule

# Find a suitable time for the meeting
def find_meeting_time(start, end, duration, blocked):
    current_time = start

    while current_time + duration <= end:
        is_blocked = False
        for period in blocked:
            if current_time < period[1] and (current_time + duration) > period[0]:
                is_blocked = True
                break
        
        if not is_blocked:
            return current_time
        
        current_time += timedelta(minutes=1)
    
    return None

# Look for a suitable time
meeting_time_start = find_meeting_time(work_start, work_end, meeting_duration, blocked_times)

if meeting_time_start:
    meeting_time_end = meeting_time_start + meeting_duration
    meeting_day = "Monday"
    print(f"{meeting_time_start.strftime('%H:%M')}:{meeting_time_end.strftime('%H:%M')} - {meeting_day}")
else:
    print("No suitable time found.")