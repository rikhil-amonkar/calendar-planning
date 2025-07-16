from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, preferred_end_time):
    # Convert meeting duration from minutes to a timedelta object
    meeting_timedelta = timedelta(minutes=meeting_duration)
    
    # Define the workday start and end times
    workday_start = datetime.strptime("09:00", "%H:%M")
    workday_end = datetime.strptime(preferred_end_time, "%H:%M")
    
    # Initialize a list to store available time slots
    available_slots = []
    
    # Iterate over each participant's schedule
    for participant, schedule in participants.items():
        current_time = workday_start
        
        # Check for gaps in the schedule
        for event_start, event_end in sorted(schedule):
            event_start_time = datetime.strptime(event_start, "%H:%M")
            event_end_time = datetime.strptime(event_end, "%H:%M")
            
            # If there's a gap between the current time and the next event, add it as an available slot
            if current_time < event_start_time:
                available_slots.append((current_time, event_start_time))
            
            # Update the current time to the end of the current event
            current_time = max(current_time, event_end_time)
        
        # Check if there's a gap between the last event and the workday end
        if current_time < workday_end:
            available_slots.append((current_time, workday_end))
    
    # Find the common available slots across all participants
    common_slots = available_slots[0]
    for slot in available_slots[1:]:
        common_start = max(common_slots[0], slot[0])
        common_end = min(common_slots[1], slot[1])
        if common_start < common_end:
            common_slots = (common_start, common_end)
        else:
            common_slots = None
            break
    
    # Check if there's a valid slot that fits the meeting duration
    if common_slots and (common_slots[1] - common_slots[0]) >= meeting_timedelta:
        meeting_start = common_slots[0].strftime("%H:%M")
        meeting_end = (common_slots[0] + meeting_timedelta).strftime("%H:%M")
        return f"{meeting_start}:{meeting_end} Monday"
    else:
        return "No suitable time found"

# Define the participants' schedules
participants = {
    "Jeffrey": [("09:30", "10:00"), ("10:30", "11:00")],
    "Virginia": [("09:00", "09:30"), ("10:00", "10:30"), ("14:30", "15:00"), ("16:00", "16:30")],
    "Melissa": [("09:00", "11:30"), ("12:00", "12:30"), ("13:00", "15:00"), ("16:00", "17:00")]
}

# Meeting duration in minutes
meeting_duration = 30

# Preferred end time for the meeting
preferred_end_time = "14:00"

# Find and print the meeting time
print(find_meeting_time(participants, meeting_duration, preferred_end_time))