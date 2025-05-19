import datetime

def find_meeting_time(ryan_schedule, adam_schedule, meeting_duration, preferred_days):
    # Convert schedules to time objects for easier manipulation
    ryan_free = set()
    for time in ryan_schedule:
        start = datetime.time(hour=time[0], minute=time[1])
        end = datetime.time(hour=time[2], minute=time[3])
        ryan_free.add((start, end))
    
    adam_free = set()
    for time in adam_schedule:
        start = datetime.time(hour=time[0], minute=time[1])
        end = datetime.time(hour=time[2], minute=time[3])
        adam_free.add((start, end))
    
    # Check each preferred day
    for day in preferred_days:
        current_day = datetime.date.weekday(day)
        # Get the available time slots for the day
        day_free = []
        for time in ryan_free:
            if time[0].date() == day and not any(adam_time[0].date() == day for adam_time in adam_free):
                day_free.append(time)
        
        # Find overlapping time slots
        for slot in day_free:
            start = slot[0]
            end = slot[1] + datetime.timedelta(minutes=meeting_duration)
            if start.time() >= end.time():
                continue
            if all(not (adam_start.date() == day and start <= adam_start < end for adam_start, adam_end in adam_free)):
                return f"{start.strftime('%H:%M')}:{end.strftime('%H:%M')}: {day}"
    
    # If no time found (though problem states there is a solution)
    return "No time found"

# Example usage
preferred_days = ["Monday", "Tuesday", "Wednesday"]
meeting_duration = datetime.timedelta(minutes=30)

ryan_schedule = [
    ("09:30", "10:00"),
    ("11:00", "12:00"),
    ("13:00", "13:30"),
    ("15:30", "16:00"),
    ("16:30", "17:00"),
    ("11:30", "12:30"),
    ("15:30", "16:00"),
    ("16:30", "17:00"),
    ("12:00", "13:00"),
    ("15:30", "16:00")
]

adam_schedule = [
    ("09:00", "10:30"),
    ("11:00", "13:30"),
    ("14:00", "16:00"),
    ("16:30", "17:00"),
    ("09:00", "10:00"),
    ("10:30", "15:30"),
    ("16:00", "17:00"),
    ("09:00", "09:30"),
    ("10:00", "11:00"),
    ("11:30", "14:30"),
    ("15:00", "15:30"),
    ("16:00", "16:30")
]

print(find_meeting_time(ryan_schedule, adam_schedule, meeting_duration, preferred_days))