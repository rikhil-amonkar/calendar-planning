from datetime import datetime, timedelta

def find_meeting_time(robert_schedule, ralph_schedule, preferred_days, meeting_duration):
    meeting_minutes = meeting_duration * 60
    for day in preferred_days:
        robert_busy = robert_schedule[day]
        ralph_busy = ralph_schedule[day]
        combined_busy = sorted(robert_busy + ralph_busy, key=lambda x: x[0])
        
        start_time = datetime.strptime("09:00", "%H:%M")
        end_time = datetime.strptime("17:00", "%H:%M")
        
        last_end = start_time
        
        for busy_start, busy_end in combined_busy:
            busy_start_dt = datetime.strptime(busy_start, "%H:%M")
            busy_end_dt = datetime.strptime(busy_end, "%H:%M")
            
            if (busy_start_dt - last_end).total_seconds() >= meeting_minutes:
                available_start = last_end.strftime("%H:%M")
                available_end = (last_end + timedelta(minutes=meeting_duration)).strftime("%H:%M")
                return f"{available_start}:{available_end}", day
            
            last_end = max(last_end, busy_end_dt)
        
        if (end_time - last_end).total_seconds() >= meeting_minutes:
            available_start = last_end.strftime("%H:%M")
            available_end = (last_end + timedelta(minutes=meeting_duration)).strftime("%H:%M")
            return f"{available_start}:{available_end}", day
    
    return None, None

robert_schedule = {
    "Monday": [("11:00", "11:30"), ("14:00", "14:30"), ("15:30", "16:00")],
    "Tuesday": [("10:30", "11:00"), ("15:00", "15:30")],
    "Wednesday": [("10:00", "11:00"), ("11:30", "12:00"), ("12:30", "13:00"), ("13:30", "14:00"), ("15:00", "15:30"), ("16:00", "16:30")]
}

ralph_schedule = {
    "Monday": [("10:00", "13:30"), ("14:00", "14:30"), ("15:00", "17:00")],
    "Tuesday": [("9:00", "9:30"), ("10:00", "10:30"), ("11:00", "11:30"), ("12:00", "13:00"), ("14:00", "15:30"), ("16:00", "17:00")],
    "Wednesday": [("10:30", "11:00"), ("11:30", "12:00"), ("13:00", "14:30"), ("16:30", "17:00")]
}

preferred_days = ["Tuesday", "Wednesday", "Monday"]  # Prioritize Tuesday and Wednesday over Monday
meeting_duration = 0.5  # 30 minutes

time, day = find_meeting_time(robert_schedule, ralph_schedule, preferred_days, meeting_duration)
print(f"Meeting time: {time}, Day: {day}")