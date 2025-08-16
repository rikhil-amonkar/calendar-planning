from datetime import datetime, timedelta

def find_meeting_time(danielle_schedule, bruce_schedule, eric_schedule, meeting_duration, work_start, work_end):
    # Convert all times to datetime objects for comparison
    work_start_dt = datetime.strptime(work_start, "%H:%M")
    work_end_dt = datetime.strptime(work_end, "%H:%M")
    
    # Parse schedules into lists of tuples (start, end)
    danielle_meetings = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in danielle_schedule]
    bruce_meetings = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in bruce_schedule]
    eric_meetings = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in eric_schedule]
    
    # Combine all schedules
    all_meetings = sorted(danielle_meetings + bruce_meetings + eric_meetings)
    
    # Find gaps in the schedule
    current_time = work_start_dt
    for meeting_start, meeting_end in all_meetings:
        if current_time < meeting_start and meeting_start - current_time >= timedelta(hours=meeting_duration):
            return current_time.strftime("%H:%M"), (current_time + timedelta(hours=meeting_duration)).strftime("%H:%M")
        current_time = max(current_time, meeting_end)
    
    # Check if there's a gap after the last meeting but before work ends
    if work_end_dt - current_time >= timedelta(hours=meeting_duration):
        return current_time.strftime("%H:%M"), (current_time + timedelta(hours=meeting_duration)).strftime("%H:%M")
    
    return None

# Define schedules and constraints
danielle_schedule = [("9:00", "10:00"), ("10:30", "11:00"), ("14:30", "15:00"), ("15:30", "16:00"), ("16:30", "17:00")]
bruce_schedule = [("11:00", "11:30"), ("12:30", "13:00"), ("14:00", "14:30"), ("15:30", "16:00")]
eric_schedule = [("9:00", "9:30"), ("10:00", "11:00"), ("11:30", "13:00"), ("14:30", "15:30")]
meeting_duration = 1  # in hours
work_start = "9:00"
work_end = "17:00"

# Find a suitable meeting time
meeting_time = find_meeting_time(danielle_schedule, bruce_schedule, eric_schedule, meeting_duration, work_start, work_end)

if meeting_time:
    print(f"{meeting_time[0]}:{meeting_time[1]} Monday")
else:
    print("No available time found.")