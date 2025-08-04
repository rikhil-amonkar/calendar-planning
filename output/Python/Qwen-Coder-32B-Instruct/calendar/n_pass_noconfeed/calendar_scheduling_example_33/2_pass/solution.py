from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, start_time, end_time, preferences):
    # Convert start_time and end_time to datetime objects
    start_time = datetime.strptime(start_time, "%H:%M")
    end_time = datetime.strptime(end_time, "%H:%M")
    
    # Initialize a list to hold all busy times
    all_busy_times = []
    
    # Collect all busy times from participants
    for person, busy_times in participants.items():
        for busy_start, busy_end in busy_times:
            all_busy_times.append((datetime.strptime(busy_start, "%H:%M"), datetime.strptime(busy_end, "%H:%M")))
    
    # Sort all busy times
    all_busy_times.sort()
    
    # Initialize variables to track the current time
    current_time = start_time
    
    # Iterate through the busy times to find gaps
    for busy_start, busy_end in all_busy_times:
        if current_time + timedelta(minutes=meeting_duration) <= busy_start:
            # Check if this slot fits any preferences
            if not preferences or any(pref[0] <= current_time.time() <= pref[1] for pref in preferences):
                return f"{current_time.strftime('%H:%M')}-{(current_time + timedelta(minutes=meeting_duration)).strftime('%H:%M')}", "Monday"
        current_time = max(current_time, busy_end)
    
    # Check the last possible slot
    if current_time + timedelta(minutes=meeting_duration) <= end_time:
        if not preferences or any(pref[0] <= current_time.time() <= pref[1] for pref in preferences):
            return f"{current_time.strftime('%H:%M')}-{(current_time + timedelta(minutes=meeting_duration)).strftime('%H:%M')}", "Monday"
    
    return None, None

# Define participants' schedules
participants = {
    "Lisa": [("09:00", "10:00"), ("10:30", "11:30"), ("12:30", "13:00"), ("16:00", "16:30")],
    "Bobby": [("09:00", "09:30"), ("10:00", "10:30"), ("11:30", "12:00"), ("15:00", "15:30")],
    "Randy": [("09:30", "10:00"), ("10:30", "11:00"), ("11:30", "12:30"), ("13:00", "13:30"), ("14:30", "15:30"), ("16:00", "16:30")]
}

# Define preferences (time range within which the meeting should be scheduled)
preferences = [(datetime.strptime("15:00", "%H:%M").time(), datetime.strptime("18:00", "%H:%M").time())]

# Define meeting duration in minutes
meeting_duration = 30

# Define work hours
start_time = "09:00"
end_time = "17:00"

# Find a suitable meeting time
meeting_time, day_of_week = find_meeting_time(participants, meeting_duration, start_time, end_time, preferences)

# Output the result
print(f"Meeting Time: {meeting_time}, Day: {day_of_week}")