from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, preferred_end_time):
    # Convert times to datetime objects for easier manipulation
    start_of_day = datetime.strptime("09:00", "%H:%M")
    end_of_day = datetime.strptime("17:00", "%H:%M")
    
    # Initialize available time slots for each participant
    available_slots = {}
    for participant, busy_times in participants.items():
        current_time = start_of_day
        available_slots[participant] = []
        for busy_start, busy_end in busy_times:
            busy_start_dt = datetime.strptime(busy_start, "%H:%M")
            busy_end_dt = datetime.strptime(busy_end, "%H:%M")
            if current_time < busy_start_dt:
                available_slots[participant].append((current_time, busy_start_dt))
            current_time = max(current_time, busy_end_dt)
        if current_time < end_of_day:
            available_slots[participant].append((current_time, end_of_day))
    
    # Find common available slots
    common_slots = available_slots[list(available_slots.keys())[0]]
    for participant, slots in available_slots.items():
        new_common_slots = []
        for slot in slots:
            for common_slot in common_slots:
                overlap_start = max(slot[0], common_slot[0])
                overlap_end = min(slot[1], common_slot[1])
                if overlap_end - overlap_start >= timedelta(minutes=meeting_duration):
                    new_common_slots.append((overlap_start, overlap_end))
        common_slots = new_common_slots
    
    # Filter slots based on preferred end time
    filtered_slots = [(start, end) for start, end in common_slots if end <= datetime.strptime(preferred_end_time, "%H:%M")]
    
    # Select the first valid slot
    if filtered_slots:
        selected_slot = filtered_slots[0]
        start_time_str = selected_slot[0].strftime("%H:%M")
        end_time_str = selected_slot[1].strftime("%H:%M")
        return f"{start_time_str}:{end_time_str} Monday"
    else:
        return "No available time slot found"

# Define participants' busy times
participants = {
    "Christine": [("09:30", "10:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:30", "15:00"), ("16:00", "16:30")],
    "Janice": [],
    "Bobby": [("12:00", "12:30"), ("14:30", "15:00")],
    "Elizabeth": [("09:00", "09:30"), ("11:30", "13:00"), ("13:30", "14:00"), ("15:00", "15:30"), ("16:00", "17:00")],
    "Tyler": [("09:00", "11:00"), ("12:00", "12:30"), ("13:00", "13:30"), ("15:30", "16:00"), ("16:30", "17:00")],
    "Edward": [("09:00", "09:30"), ("10:00", "11:00"), ("11:30", "14:00"), ("14:30", "15:30"), ("16:00", "17:00")]
}

# Meeting duration in minutes
meeting_duration = 30

# Preferred end time
preferred_end_time = "13:00"

# Find and print the meeting time
print(find_meeting_time(participants, meeting_duration, preferred_end_time))