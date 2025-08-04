from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, work_start, work_end):
    # Convert work hours to datetime objects
    work_start = datetime.strptime(work_start, "%H:%M")
    work_end = datetime.strptime(work_end, "%H:%M")
    
    # Initialize available times for each participant
    available_times = {}
    
    for name, blocks in participants.items():
        current_time = work_start
        available_times[name] = []
        
        for block in blocks:
            block_start, block_end = map(lambda x: datetime.strptime(x, "%H:%M"), block)
            
            if current_time < block_start:
                available_times[name].append((current_time, block_start))
            
            current_time = max(current_time, block_end)
        
        if current_time < work_end:
            available_times[name].append((current_time, work_end))
    
    # Find common available times
    common_available_times = available_times[next(iter(available_times))]
    
    for name, times in available_times.items():
        common_available_times = [
            (max(t1[0], t2[0]), min(t1[1], t2[1]))
            for t1 in common_available_times
            for t2 in times
            if max(t1[0], t2[0]) < min(t1[1], t2[1])
        ]
    
    # Find a time slot that fits the meeting duration
    for start, end in common_available_times:
        if (end - start) >= timedelta(minutes=meeting_duration):
            return f"{start.strftime('%H:%M')}:{end.strftime('%H:%M')}", "Monday"
    
    return None, None

# Participants' schedules
participants = {
    "Gregory": [("9:00", "10:00"), ("10:30", "11:30"), ("12:30", "13:00"), ("13:30", "14:00")],
    "Natalie": [],
    "Christine": [("9:00", "11:30"), ("13:30", "17:00")],
    "Vincent": [("9:00", "9:30"), ("10:30", "12:00"), ("12:30", "14:00"), ("14:30", "17:00")]
}

meeting_duration = 30  # in minutes
work_start = "9:00"
work_end = "17:00"

meeting_time, day_of_week = find_meeting_time(participants, meeting_duration, work_start, work_end)
print(f"{meeting_time}, {day_of_week}")