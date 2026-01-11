from datetime import datetime, timedelta

def find_meeting_time(participants_busy_times, meeting_duration=60, start_time="09:00", end_time="17:00", day="Monday"):
    # Convert start and end times to datetime objects
    start_datetime = datetime.strptime(start_time, "%H:%M")
    end_datetime = datetime.strptime(end_time, "%H:%M")
    
    # Create a list of all busy times
    all_busy_times = []
    for busy_times in participants_busy_times.values():
        all_busy_times.extend(busy_times)
    
    # Sort all busy times by start time
    all_busy_times.sort()
    
    # Initialize variables to track the current time
    current_time = start_datetime
    while current_time + timedelta(minutes=meeting_duration) <= end_datetime:
        # Check if the current time is busy
        is_busy = False
        for busy_start, busy_end in all_busy_times:
            busy_start_dt = datetime.strptime(busy_start, "%H:%M")
            busy_end_dt = datetime.strptime(busy_end, "%H:%M")
            if busy_start_dt <= current_time < busy_end_dt:
                # Move current_time to the end of the busy period
                current_time = busy_end_dt
                is_busy = True
                break
        
        if not is_busy:
            # Found a free slot
            meeting_start = current_time.strftime("%H:%M")
            meeting_end = (current_time + timedelta(minutes=meeting_duration)).strftime("%H:%M")
            return f"{meeting_start}:{meeting_end} {day}"
        
        # Move to the next minute
        current_time += timedelta(minutes=1)
    
    return "No available time slot found"

# Define busy times for each participant
participants_busy_times = {
    "Joshua": [("11:00", "12:30"), ("13:30", "14:30"), ("16:30", "17:00")],
    "Jerry": [("9:00", "9:30"), ("10:30", "12:00"), ("12:30", "13:00"), ("13:30", "14:00"), ("14:30", "15:00"), ("15:30", "16:00")],
    "Jesse": [("9:00", "9:30"), ("10:30", "12:00"), ("12:30", "13:00"), ("14:30", "15:00"), ("15:30", "16:30")],
    "Kenneth": [("10:30", "12:30"), ("13:30", "14:00"), ("14:30", "15:00"), ("15:30", "16:00"), ("16:30", "17:00")]
}

# Find and print the meeting time
meeting_time = find_meeting_time(participants_busy_times)
print(meeting_time)