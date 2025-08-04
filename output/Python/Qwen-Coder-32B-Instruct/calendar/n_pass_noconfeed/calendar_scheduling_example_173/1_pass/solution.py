from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, start_time, end_time, constraints):
    # Convert times to datetime objects for easier manipulation
    start_time = datetime.strptime(start_time, "%H:%M")
    end_time = datetime.strptime(end_time, "%H:%M")
    
    # Initialize available time slots
    available_slots = []
    
    # Create a time slot for every possible meeting start time
    current_time = start_time
    while current_time + timedelta(minutes=meeting_duration) <= end_time:
        available_slots.append(current_time)
        current_time += timedelta(minutes=30)  # Assuming we check every 30 minutes
    
    # Filter available slots based on participants' schedules and constraints
    valid_slots = available_slots.copy()
    for person, busy_times in participants.items():
        for busy_start, busy_end in busy_times:
            busy_start = datetime.strptime(busy_start, "%H:%M")
            busy_end = datetime.strptime(busy_end, "%H:%M")
            for slot in available_slots:
                slot_end = slot + timedelta(minutes=meeting_duration)
                if slot < busy_end and slot_end > busy_start:
                    if slot in valid_slots:
                        valid_slots.remove(slot)
    
    # Apply additional constraints
    for constraint in constraints:
        if constraint == "Harold do not want to meet on Monday after 13:00":
            cutoff_time = datetime.strptime("13:00", "%H:%M")
            valid_slots = [slot for slot in valid_slots if slot < cutoff_time]
    
    # Output the first valid slot found
    if valid_slots:
        meeting_start = valid_slots[0].strftime("%H:%M")
        meeting_end = (valid_slots[0] + timedelta(minutes=meeting_duration)).strftime("%H:%M")
        print(f"{meeting_start}:{meeting_end} Monday")
    else:
        print("No available time slot found.")

# Define participants' schedules and constraints
participants = {
    "Jacqueline": [("9:00", "9:30"), ("11:00", "11:30"), ("12:30", "13:00"), ("15:30", "16:00")],
    "Harold": [("10:00", "10:30"), ("13:00", "13:30"), ("15:00", "17:00")],
    "Arthur": [("9:00", "9:30"), ("10:00", "12:30"), ("14:30", "15:00"), ("15:30", "17:00")],
    "Kelly": [("9:00", "9:30"), ("10:00", "11:00"), ("11:30", "12:30"), ("14:00", "15:00"), ("15:30", "16:00")]
}

constraints = [
    "Harold do not want to meet on Monday after 13:00"
]

# Call the function to find a meeting time
find_meeting_time(participants, 30, "9:00", "17:00", constraints)