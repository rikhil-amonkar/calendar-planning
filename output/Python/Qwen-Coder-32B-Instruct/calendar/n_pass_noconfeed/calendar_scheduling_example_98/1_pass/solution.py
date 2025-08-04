from datetime import datetime, timedelta

def find_meeting_time(juan_schedule, marilyn_schedule, ronald_schedule, meeting_duration, day):
    # Convert times to datetime objects for easier manipulation
    def parse_time(time_str):
        return datetime.strptime(f"{day} {time_str}", "%A %H:%M")
    
    juan_busy = [(parse_time(start), parse_time(end)) for start, end in juan_schedule]
    marilyn_busy = [(parse_time(start), parse_time(end)) for start, end in marilyn_schedule]
    ronald_busy = [(parse_time(start), parse_time(end)) for start, end in ronald_schedule]
    
    # Define the work day window
    work_start = parse_time("09:00")
    work_end = parse_time("16:00")
    
    # Iterate over possible meeting start times
    current_time = work_start
    while current_time + timedelta(minutes=meeting_duration) <= work_end:
        # Check if the current time slot is free for all
        if all(current_time < busy[0] or current_time + timedelta(minutes=meeting_duration) > busy[1]
               for busy in juan_busy + marilyn_busy + ronald_busy):
            # Found a suitable time
            meeting_start = current_time.strftime("%H:%M")
            meeting_end = (current_time + timedelta(minutes=meeting_duration)).strftime("%H:%M")
            return f"{meeting_start}:{meeting_end} {day}"
        current_time += timedelta(minutes=1)
    
    return "No available time found"

# Define schedules
juan_schedule = [("09:00", "10:30"), ("15:30", "16:00")]
marilyn_schedule = [("11:00", "11:30"), ("12:30", "13:00")]
ronald_schedule = [("09:00", "10:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:00", "16:30")]

# Meeting details
meeting_duration = 30  # in minutes
day = "Monday"

# Find and print the meeting time
print(find_meeting_time(juan_schedule, marilyn_schedule, ronald_schedule, meeting_duration, day))