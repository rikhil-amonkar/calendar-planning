from datetime import datetime, timedelta

def find_meeting_time(julie_schedule, sean_schedule, lori_schedule, meeting_duration):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    
    # Convert blocked times to datetime objects
    julie_blocked_times = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in julie_schedule]
    sean_blocked_times = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in sean_schedule]
    lori_blocked_times = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in lori_schedule]
    
    current_time = work_start
    while current_time + timedelta(hours=meeting_duration) <= work_end:
        available_for_all = True
        for blocked_times in [julie_blocked_times, sean_blocked_times, lori_blocked_times]:
            if any(current_time < end and current_time + timedelta(hours=meeting_duration) > start for start, end in blocked_times):
                available_for_all = False
                break
        if available_for_all:
            return current_time.strftime("%H:%M"), (current_time + timedelta(hours=meeting_duration)).strftime("%H:%M")
        current_time += timedelta(minutes=30)  # Check every 30 minutes for availability
    
    return None, None

# Schedules in the format of ("start_time", "end_time")
julie_schedule = [("09:00", "09:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("13:30", "14:00"), ("16:00", "17:00")]
sean_schedule = [("09:00", "09:30"), ("13:00", "13:30"), ("15:00", "15:30"), ("16:00", "16:30")]
lori_schedule = [("10:00", "10:30"), ("11:00", "13:00"), ("15:30", "17:00")]

meeting_duration = 1  # Duration in hours

start_time, end_time = find_meeting_time(julie_schedule, sean_schedule, lori_schedule, meeting_duration)
if start_time and end_time:
    print(f"{start_time}:{end_time} Monday")
else:
    print("No available time found.")