from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, work_start, work_end, day_of_week):
    # Convert times to datetime objects for easier manipulation
    work_start = datetime.strptime(work_start, "%H:%M")
    work_end = datetime.strptime(work_end, "%H:%M")
    meeting_duration = timedelta(hours=meeting_duration)
    
    # Initialize available time slots
    available_slots = []
    
    # Find available slots for each person
    for person, blocks in schedules.items():
        current_time = work_start
        for block in blocks:
            block_start, block_end = map(lambda x: datetime.strptime(x, "%H:%M"), block)
            if current_time < block_start:
                available_slots.append((person, current_time, block_start))
            current_time = max(current_time, block_end)
        if current_time < work_end:
            available_slots.append((person, current_time, work_end))
    
    # Group available slots by time
    time_slots = {}
    for person, start, end in available_slots:
        if start not in time_slots:
            time_slots[start] = []
        time_slots[start].append((end, person))
    
    # Find a common slot that fits all participants
    for start, ends in sorted(time_slots.items()):
        if len(ends) == len(schedules):
            end_times = [end for end, _ in ends]
            earliest_end = min(end_times)
            if earliest_end - start >= meeting_duration:
                return f"{start.strftime('%H:%M')}:{earliest_end.strftime('%H:%M')}", day_of_week
    
    return None, None

# Define schedules, meeting duration, work hours, and day of the week
schedules = {
    "Olivia": [("12:30", "13:30"), ("14:30", "15:00"), ("16:30", "17:00")],
    "Anna": [],
    "Virginia": [("9:00", "10:00"), ("11:30", "16:00"), ("16:30", "17:00")],
    "Paul": [("9:00", "9:30"), ("11:00", "11:30"), ("13:00", "14:00"), ("14:30", "16:00"), ("16:30", "17:00")]
}
meeting_duration = 1
work_start = "9:00"
work_end = "17:00"
day_of_week = "Monday"

# Find and print the meeting time
meeting_time, day = find_meeting_time(schedules, meeting_duration, work_start, work_end, day_of_week)
print(f"{meeting_time}, {day}")