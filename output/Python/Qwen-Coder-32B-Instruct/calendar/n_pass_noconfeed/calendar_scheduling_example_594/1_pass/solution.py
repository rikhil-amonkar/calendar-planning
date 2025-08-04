from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, work_start, work_end):
    # Convert times to datetime objects for easier manipulation
    work_start = datetime.strptime(work_start, "%H:%M")
    work_end = datetime.strptime(work_end, "%H:%M")
    meeting_duration = timedelta(minutes=meeting_duration)
    
    # Initialize available time slots
    available_slots = []
    
    # Find available slots for each person
    for person, busy_times in schedules.items():
        current_time = work_start
        for start, end in busy_times:
            start = datetime.strptime(start, "%H:%M")
            end = datetime.strptime(end, "%H:%M")
            
            if current_time < start:
                available_slots.append((current_time, start))
            current_time = max(current_time, end)
        
        if current_time < work_end:
            available_slots.append((current_time, work_end))
    
    # Find common slots
    common_slots = available_slots[::len(schedules)]
    for i in range(1, len(available_slots) // len(schedules)):
        common_slots = [(max(slot1[0], slot2[0]), min(slot1[1], slot2[1])) 
                        for slot1, slot2 in zip(common_slots, available_slots[i::len(schedules)]) 
                        if max(slot1[0], slot2[0]) < min(slot1[1], slot2[1])]
    
    # Find the first slot that fits the meeting duration
    for start, end in common_slots:
        if end - start >= meeting_duration:
            return f"{start.strftime('%H:%M')}:{(start + meeting_duration).strftime('%H:%M')}", "Monday"
    
    return None, None

# Schedules in the format of (start, end) times
schedules = {
    "Adam": [("09:30", "10:00"), ("12:30", "13:00"), ("14:30", "15:00"), ("16:30", "17:00")],
    "Roy": [("10:00", "11:00"), ("11:30", "13:00"), ("13:30", "14:30"), ("16:30", "17:00")]
}

meeting_time, day_of_week = find_meeting_time(schedules, 30, "09:00", "17:00")
print(f"{meeting_time}, {day_of_week}")