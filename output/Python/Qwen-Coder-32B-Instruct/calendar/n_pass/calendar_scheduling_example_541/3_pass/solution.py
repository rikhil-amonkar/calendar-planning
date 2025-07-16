from datetime import datetime, timedelta

def find_meeting_time(kayla_schedule, rebecca_schedule, meeting_duration, work_start, work_end):
    # Convert times to datetime objects for easier manipulation
    work_start = datetime.strptime(work_start, "%H:%M")
    work_end = datetime.strptime(work_end, "%H:%M")
    kayla_blocked_times = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in kayla_schedule]
    rebecca_blocked_times = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in rebecca_schedule]
    
    # Initialize current time to the start of workday
    current_time = work_start
    
    while current_time < work_end - timedelta(hours=meeting_duration):
        # Check if current time is free for both
        kayla_free = all(current_time < k[0] or current_time + timedelta(hours=meeting_duration) <= k[1] for k in kayla_blocked_times)
        rebecca_free = all(current_time < r[0] or current_time + timedelta(hours=meeting_duration) <= r[1] for r in rebecca_blocked_times)
        
        # Check for Rebecca's specific blocked time from 13:30 to 15:00
        rebecca_blocked_13_5_to_15 = datetime.strptime("13:30", "%H:%M") <= current_time < datetime.strptime("15:00", "%H:%M")
        
        if kayla_free and rebecca_free and not rebecca_blocked_13_5_to_15:
            # Found a common free slot
            meeting_start = current_time.strftime("%H:%M")
            meeting_end = (current_time + timedelta(hours=meeting_duration)).strftime("%H:%M")
            return f"{meeting_start}:{meeting_end} Monday"
        
        # Move to the next possible start time
        current_time += timedelta(minutes=30)

# Define the schedules and constraints
kayla_schedule = [("10:00", "10:30"), ("14:30", "16:00")]
rebecca_schedule = [("9:00", "13:00"), ("13:30", "15:00"), ("15:30", "16:00")]
meeting_duration = 1  # in hours
work_start = "9:00"
work_end = "17:00"

# Find and print the meeting time
print(find_meeting_time(kayla_schedule, rebecca_schedule, meeting_duration, work_start, work_end))