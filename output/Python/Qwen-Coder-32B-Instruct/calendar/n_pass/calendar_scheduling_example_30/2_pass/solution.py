from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, preferred_end_time):
    # Convert meeting duration from minutes to a timedelta object
    meeting_timedelta = timedelta(minutes=meeting_duration)
    
    # Define the workday start and end times
    workday_start = datetime.strptime("09:00", "%H:%M")
    workday_end = datetime.strptime(preferred_end_time, "%H:%M")
    
    def get_available_slots(schedule):
        current_time = workday_start
        available_slots = []
        
        for event_start, event_end in sorted(schedule):
            event_start_time = datetime.strptime(event_start, "%H:%M")
            event_end_time = datetime.strptime(event_end, "%H:%M")
            
            if current_time < event_start_time:
                available_slots.append((current_time, event_start_time))
            
            current_time = max(current_time, event_end_time)
        
        if current_time < workday_end:
            available_slots.append((current_time, workday_end))
        
        return available_slots
    
    # Get available slots for each participant
    all_available_slots = [get_available_slots(schedule) for schedule in participants.values()]
    
    # Find the intersection of all available slots
    common_slots = all_available_slots[0]
    for slots in all_available_slots[1:]:
        new_common_slots = []
        for slot1 in common_slots:
            for slot2 in slots:
                common_start = max(slot1[0], slot2[0])
                common_end = min(slot1[1], slot2[1])
                if common_start < common_end:
                    new_common_slots.append((common_start, common_end))
        common_slots = new_common_slots
    
    # Check if there's a valid slot that fits the meeting duration
    for slot in common_slots:
        if (slot[1] - slot[0]) >= meeting_timedelta:
            meeting_start = slot[0].strftime("%H:%M")
            meeting_end = (slot[0] + meeting_timedelta).strftime("%H:%M")
            return f"{meeting_start} - {meeting_end} Monday"
    
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