from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, preferred_start_time):
    day_of_week = "Monday"
    start_time = datetime.strptime("09:00", "%H:%M")
    end_time = datetime.strptime("17:00", "%H:%M")
    
    while start_time + timedelta(minutes=meeting_duration) <= end_time:
        available = True
        for person, schedule in participants.items():
            for busy_start, busy_end in schedule:
                busy_start_dt = datetime.strptime(busy_start, "%H:%M")
                busy_end_dt = datetime.strptime(busy_end, "%H:%M")
                if start_time < busy_end_dt and start_time + timedelta(minutes=meeting_duration) > busy_start_dt:
                    available = False
                    break
            if not available:
                break
        
        if available and start_time >= preferred_start_time:
            return f"{start_time.strftime('%H:%M')}:{(start_time + timedelta(minutes=meeting_duration)).strftime('%H:%M')}", day_of_week
        
        start_time += timedelta(minutes=15)
    
    return None, None

participants = {
    "Daniel": [],
    "Kathleen": [("14:30", "15:30")],
    "Carolyn": [("12:00", "12:30"), ("13:00", "13:30")],
    "Roger": [],
    "Cheryl": [("9:00", "9:30"), ("10:00", "11:30"), ("12:30", "13:30"), ("14:00", "17:00")],
    "Virginia": [("9:30", "11:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:30", "15:30"), ("16:00", "17:00")],
    "Angela": [("9:30", "10:00"), ("10:30", "11:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:00", "16:30")]
}

meeting_duration = 30
preferred_start_time = datetime.strptime("12:30", "%H:%M")

time, day = find_meeting_time(participants, meeting_duration, preferred_start_time)
print(f"{time}, {day}")