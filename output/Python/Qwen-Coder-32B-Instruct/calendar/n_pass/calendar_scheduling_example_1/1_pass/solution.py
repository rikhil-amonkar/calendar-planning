from datetime import datetime, timedelta

def find_meeting_time(raymond_schedule, billy_schedule, donald_schedule, preferred_end_time):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    meeting_duration = timedelta(minutes=30)
    
    # Convert all times to datetime objects for easier comparison
    raymond_busy = [tuple(datetime.strptime(t, "%H:%M") for t in slot) for slot in raymond_schedule]
    billy_busy = [tuple(datetime.strptime(t, "%H:%M") for t in slot) for slot in billy_schedule]
    donald_busy = [tuple(datetime.strptime(t, "%H:%M") for t in slot) for slot in donald_schedule]
    
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        if current_time.hour >= preferred_end_time:
            break
        if not any(current_time < end and current_time + meeting_duration > start for start, end in raymond_busy) and \
           not any(current_time < end and current_time + meeting_duration > start for start, end in billy_busy) and \
           not any(current_time < end and current_time + meeting_duration > start for start, end in donald_busy):
            return f"{current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')}", "Monday"
        current_time += timedelta(minutes=30)
    
    return None, None

raymond_schedule = [("09:00", "09:30"), ("11:30", "12:00"), ("13:00", "13:30"), ("15:00", "15:30")]
billy_schedule = [("10:00", "10:30"), ("12:00", "13:00"), ("16:30", "17:00")]
donald_schedule = [("09:00", "09:30"), ("10:00", "11:00"), ("12:00", "13:00"), ("14:00", "14:30"), ("16:00", "17:00")]

meeting_time, day_of_week = find_meeting_time(raymond_schedule, billy_schedule, donald_schedule, 15)
print(f"{meeting_time}:{day_of_week}")