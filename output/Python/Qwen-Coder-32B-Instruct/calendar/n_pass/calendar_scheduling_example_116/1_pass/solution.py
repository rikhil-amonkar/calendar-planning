from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, preferred_start_time):
    day_of_week = "Monday"
    start_time = datetime.strptime("09:00", "%H:%M")
    end_time = datetime.strptime("17:00", "%H:%M")
    meeting_duration = timedelta(minutes=meeting_duration)
    
    while start_time + meeting_duration <= end_time:
        available = True
        for person, busy_times in participants.items():
            for busy_start, busy_end in busy_times:
                busy_start_dt = datetime.strptime(busy_start, "%H:%M")
                busy_end_dt = datetime.strptime(busy_end, "%H:%M")
                if start_time < busy_end_dt and start_time + meeting_duration > busy_start_dt:
                    available = False
                    break
            if not available:
                break
        
        if available and start_time >= datetime.strptime(preferred_start_time, "%H:%M"):
            return f"{start_time.strftime('%H:%M')}:{(start_time + meeting_duration).strftime('%H:%M')}", day_of_week
        
        start_time += timedelta(minutes=30)

participants = {
    "Adam": [("14:00", "15:00")],
    "John": [("13:00", "13:30"), ("14:00", "14:30"), ("15:30", "16:00"), ("16:30", "17:00")],
    "Stephanie": [("9:30", "10:00"), ("10:30", "11:00"), ("11:30", "16:00"), ("16:30", "17:00")],
    "Anna": [("9:30", "10:00"), ("12:00", "12:30"), ("13:00", "15:30"), ("16:30", "17:00")]
}

meeting_time, day_of_week = find_meeting_time(participants, 30, "14:30")
print(f"{meeting_time}, {day_of_week}")