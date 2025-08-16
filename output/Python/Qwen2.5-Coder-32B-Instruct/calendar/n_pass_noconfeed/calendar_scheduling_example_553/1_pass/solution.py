from datetime import datetime, timedelta

def find_meeting_time(eric_schedule, henry_schedule, meeting_duration, preferred_end_time):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime(preferred_end_time, "%H:%M")
    meeting_duration = timedelta(minutes=meeting_duration)
    
    # Convert schedule strings to datetime objects
    eric_blocked_times = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in eric_schedule]
    henry_blocked_times = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in henry_schedule]
    
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        available = True
        for start, end in eric_blocked_times + henry_blocked_times:
            if start <= current_time < end or start < current_time + meeting_duration <= end:
                available = False
                break
        if available:
            return current_time.strftime("%H:%M"), (current_time + meeting_duration).strftime("%H:%M"), "Monday"
        current_time += timedelta(minutes=15)  # Check every 15 minutes for availability
    
    return None

eric_schedule = [("12:00", "13:00"), ("14:00", "15:00")]
henry_schedule = [("09:30", "10:00"), ("10:30", "11:00"), ("11:30", "12:30"), ("13:00", "13:30"), ("14:30", "15:00"), ("16:00", "17:00")]
meeting_duration = 30  # in minutes
preferred_end_time = "10:00"

meeting_start, meeting_end, day_of_week = find_meeting_time(eric_schedule, henry_schedule, meeting_duration, preferred_end_time)
print(f"{meeting_start}:{meeting_end}, {day_of_week}")