from datetime import datetime, timedelta

def find_meeting_time():
    # Define the work hours
    start_time = datetime.strptime("09:00", "%H:%M")
    end_time = datetime.strptime("17:00", "%H:%M")
    
    # Define Harold's busy times
    harold_busy_times = {
        "Monday": [
            (datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
            (datetime.strptime("10:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
        ],
        "Tuesday": [
            (datetime.strptime("00:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),  # Updated to cover the entire unavailable period
            (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
            (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
            (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
            (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
        ]
    }
    
    # Meeting duration
    meeting_duration = timedelta(minutes=30)
    
    # Preference: Avoid Monday, prefer Tuesday before 14:30
    preferred_day = "Tuesday"
    preferred_end_time = datetime.strptime("14:30", "%H:%M")
    
    # Check available times
    for day in ["Monday", "Tuesday"]:
        current_time = start_time
        while current_time < end_time - meeting_duration:
            is_free = True
            for busy_start, busy_end in harold_busy_times[day]:
                if current_time < busy_end and current_time + meeting_duration > busy_start:
                    is_free = False
                    current_time = busy_end
                    break
            if is_free:
                if day == preferred_day and current_time + meeting_duration <= preferred_end_time:
                    return f"{current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%M')}", day
                elif day != preferred_day:
                    return f"{current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%M')}", day
            current_time += timedelta(minutes=15)  # Check every 15 minutes for availability

meeting_time, meeting_day = find_meeting_time()
print(f"{meeting_time} {meeting_day}")