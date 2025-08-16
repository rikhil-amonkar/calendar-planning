from datetime import datetime, timedelta

def find_meeting_time(lisa_schedule, anthony_schedule, meeting_duration, work_start, work_end):
    # Convert times to datetime objects for easier manipulation
    work_start = datetime.strptime(work_start, "%H:%M")
    work_end = datetime.strptime(work_end, "%H:%M")
    meeting_duration = timedelta(minutes=meeting_duration)
    
    # Parse schedules into lists of tuples (start, end)
    lisa_busy = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in lisa_schedule]
    anthony_busy = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in anthony_schedule]
    
    # Function to merge busy times
    def merge_times(busy_times):
        busy_times.sort()
        merged = []
        for start, end in busy_times:
            if not merged or merged[-1][1] < start:
                merged.append((start, end))
            else:
                merged[-1] = (merged[-1][0], max(merged[-1][1], end))
        return merged
    
    # Merge busy times for both participants
    all_busy = merge_times(lisa_busy + anthony_busy)
    
    # Find free slots
    current_time = work_start
    for start, end in all_busy:
        if current_time < start:
            if start - current_time >= meeting_duration:
                return current_time.strftime("%H:%M"), (current_time + meeting_duration).strftime("%H:%M")
        current_time = max(current_time, end)
    
    # Check after last busy period
    if work_end - current_time >= meeting_duration:
        return current_time.strftime("%H:%M"), (current_time + meeting_duration).strftime("%H:%M")
    
    return None

# Example usage
lisa_schedule = [("9:00", "9:30"), ("10:30", "11:00"), ("14:00", "16:00")]
anthony_schedule = [("9:00", "9:30"), ("11:00", "11:30"), ("12:30", "13:30"), ("14:00", "15:00"), ("15:30", "16:00"), ("16:30", "17:00")]
meeting_duration = 30
work_start = "9:00"
work_end = "17:00"

meeting_start, meeting_end = find_meeting_time(lisa_schedule, anthony_schedule, meeting_duration, work_start, work_end)
print(f"{meeting_start}:{meeting_end} Monday")