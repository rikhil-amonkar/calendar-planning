from datetime import datetime, timedelta

def find_meeting_time(cheryl_schedule, james_schedule, meeting_duration, preferred_days, unavailable_days):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    
    # Combine schedules into a single list of tuples (start, end)
    combined_schedule = []
    for day in preferred_days:
        if day not in unavailable_days:
            combined_schedule.extend(james_schedule[day])
    
    # Sort the schedule by start time
    combined_schedule.sort()
    
    # Iterate through the sorted schedule to find gaps
    current_time = work_start
    for event in combined_schedule:
        event_start, event_end = map(lambda x: datetime.strptime(x, "%H:%M"), event)
        
        # Check if there's a gap between current_time and the next event
        if (event_start - current_time) >= timedelta(minutes=meeting_duration):
            # Found a suitable time slot
            meeting_start = current_time.strftime("%H:%M")
            meeting_end = (current_time + timedelta(minutes=meeting_duration)).strftime("%H:%M")
            return f"{meeting_start}:{meeting_end}", preferred_days[0]
        
        # Move current_time to the end of the current event if it's later
        if event_end > current_time:
            current_time = event_end
    
    # Check the last possible gap from the last event to work end
    if (work_end - current_time) >= timedelta(minutes=meeting_duration):
        meeting_start = current_time.strftime("%H:%M")
        meeting_end = (current_time + timedelta(minutes=meeting_duration)).strftime("%H:%M")
        return f"{meeting_start}:{meeting_end}", preferred_days[0]
    
    return None, None

# Define the schedules
cheryl_schedule = {
    "Monday": [],
    "Tuesday": [],
    "Wednesday": [],
    "Thursday": []
}

james_schedule = {
    "Monday": [("09:00", "09:30"), ("10:30", "11:00"), ("12:30", "13:00"), ("14:30", "15:30"), ("16:30", "17:00")],
    "Tuesday": [("09:00", "11:00"), ("11:30", "12:00"), ("12:30", "15:30"), ("16:00", "17:00")],
    "Wednesday": [("10:00", "11:00"), ("12:00", "13:00"), ("13:30", "16:00")],
    "Thursday": [("09:30", "11:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:00", "14:30"), ("16:30", "17:00")]
}

# Meeting details
meeting_duration = 30  # in minutes
preferred_days = ["Monday", "Tuesday"]
unavailable_days = ["Wednesday", "Thursday"]

# Find a suitable meeting time
meeting_time, meeting_day = find_meeting_time(cheryl_schedule, james_schedule, meeting_duration, preferred_days, unavailable_days)

print(f"Meeting Time: {meeting_time}, Day: {meeting_day}")