from datetime import datetime, timedelta

def find_meeting_time(lisa_schedule, anthony_schedule, meeting_duration, work_start, work_end):
    # Convert times to datetime objects for easier manipulation
    def parse_time(time_str):
        return datetime.strptime(time_str, "%H:%M")
    
    work_start = parse_time(work_start)
    work_end = parse_time(work_end)
    meeting_duration = timedelta(minutes=meeting_duration)
    
    # Parse and convert busy times to datetime objects
    lisa_busy_times = [(parse_time(start), parse_time(end)) for start, end in lisa_schedule]
    anthony_busy_times = [(parse_time(start), parse_time(end)) for start, end in anthony_schedule]
    
    # Find common free times
    current_time = work_start
    while current_time < work_end:
        lisa_free = all(current_time + meeting_duration <= start or current_time >= end for start, end in lisa_busy_times)
        anthony_free = all(current_time + meeting_duration <= start or current_time >= end for start, end in anthony_busy_times)
        
        if lisa_free and anthony_free:
            meeting_start = current_time.strftime("%H:%M")
            meeting_end = (current_time + meeting_duration).strftime("%H:%M")
            return f"{meeting_start}:{meeting_end}", "Monday"
        
        current_time += timedelta(minutes=1)
    
    return None, None

# Define schedules and constraints
lisa_schedule = [("9:00", "9:30"), ("10:30", "11:00"), ("14:00", "16:00")]
anthony_schedule = [("9:00", "9:30"), ("11:00", "11:30"), ("12:30", "13:30"), ("14:00", "15:00"), ("15:30", "16:00"), ("16:30", "17:00")]
meeting_duration = 30
work_start = "9:00"
work_end = "17:00"

# Find and print the meeting time
meeting_time, day_of_week = find_meeting_time(lisa_schedule, anthony_schedule, meeting_duration, work_start, work_end)
print(meeting_time, day_of_week)