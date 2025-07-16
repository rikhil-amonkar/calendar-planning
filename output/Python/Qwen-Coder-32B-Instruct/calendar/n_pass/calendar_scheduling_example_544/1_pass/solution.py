from datetime import datetime, timedelta

def find_meeting_time(deborah_schedule, albert_schedule, meeting_duration, max_time):
    # Convert times to datetime objects for easier manipulation
    start_time = datetime.strptime("09:00", "%H:%M")
    max_time = datetime.strptime(max_time, "%H:%M")
    meeting_duration = timedelta(minutes=meeting_duration)
    
    # Parse available times for Albert
    albert_available_times = []
    current_start = start_time
    
    for block in albert_schedule:
        block_start, block_end = map(lambda x: datetime.strptime(x, "%H:%M"), block.split("-"))
        if current_start < block_start:
            albert_available_times.append((current_start, block_start))
        current_start = max(current_start, block_end)
    
    if current_start < max_time:
        albert_available_times.append((current_start, max_time))
    
    # Find a common slot
    for albert_start, albert_end in albert_available_times:
        if albert_end - albert_start >= meeting_duration:
            return albert_start.strftime("%H:%M"), (albert_start + meeting_duration).strftime("%H:%M")
    
    return None

# Define schedules and constraints
deborah_schedule = []  # Deborah is free all day
albert_schedule = ["09:00-10:00", "10:30-12:00", "15:00-16:30"]
meeting_duration = 30  # 30 minutes
max_time = "11:00"  # Albert cannot meet after 11:00

# Find a suitable meeting time
meeting_start, meeting_end = find_meeting_time(deborah_schedule, albert_schedule, meeting_duration, max_time)

# Output the result
print(f"{meeting_start}:{meeting_end} Monday")