from datetime import datetime, timedelta

def find_meeting_time(anthony_schedule, pamela_schedule, zachary_schedule, meeting_duration, day_of_week, pamela_preference):
    start_time = datetime.strptime(f"{day_of_week} 09:00", "%A %H:%M")
    end_time = datetime.strptime(f"{day_of_week} 17:00", "%A %H:%M")
    current_time = start_time
    
    while current_time < end_time - meeting_duration:
        anthony_free = all(current_time < s or current_time + meeting_duration > e for s, e in anthony_schedule)
        pamela_free = all(current_time < s or current_time + meeting_duration > e for s, e in pamela_schedule) and current_time + meeting_duration <= pamela_preference
        zachary_free = all(current_time < s or current_time + meeting_duration > e for s, e in zachary_schedule)
        
        if anthony_free and pamela_free and zachary_free:
            return current_time.strftime("%H:%M"), (current_time + meeting_duration).strftime("%H:%M"), day_of_week
        
        current_time += timedelta(minutes=15)  # Check every 15 minutes for availability
    
    return None

# Define schedules as tuples of (start_time, end_time)
anthony_schedule = [
    (datetime.strptime("Monday 09:30", "%A %H:%M"), datetime.strptime("Monday 10:00", "%A %H:%M")),
    (datetime.strptime("Monday 12:00", "%A %H:%M"), datetime.strptime("Monday 13:00", "%A %H:%M")),
    (datetime.strptime("Monday 16:00", "%A %H:%M"), datetime.strptime("Monday 16:30", "%A %H:%M"))
]

pamela_schedule = [
    (datetime.strptime("Monday 09:30", "%A %H:%M"), datetime.strptime("Monday 10:00", "%A %H:%M")),
    (datetime.strptime("Monday 16:30", "%A %H:%M"), datetime.strptime("Monday 17:00", "%A %H:%M"))
]

zachary_schedule = [
    (datetime.strptime("Monday 09:00", "%A %H:%M"), datetime.strptime("Monday 11:30", "%A %H:%M")),
    (datetime.strptime("Monday 12:00", "%A %H:%M"), datetime.strptime("Monday 12:30", "%A %H:%M")),
    (datetime.strptime("Monday 13:00", "%A %H:%M"), datetime.strptime("Monday 13:30", "%A %H:%M")),
    (datetime.strptime("Monday 14:30", "%A %H:%M"), datetime.strptime("Monday 15:00", "%A %H:%M")),
    (datetime.strptime("Monday 16:00", "%A %H:%M"), datetime.strptime("Monday 17:00", "%A %H:%M"))
]

meeting_duration = timedelta(hours=1)
day_of_week = "Monday"
pamela_preference = datetime.strptime("Monday 14:30", "%A %H:%M")

result = find_meeting_time(anthony_schedule, pamela_schedule, zachary_schedule, meeting_duration, day_of_week, pamela_preference)
if result:
    meeting_start, meeting_end, meeting_day = result
    print(f"Meeting from {meeting_start} to {meeting_end} on {meeting_day}")
else:
    print("No available meeting time found.")