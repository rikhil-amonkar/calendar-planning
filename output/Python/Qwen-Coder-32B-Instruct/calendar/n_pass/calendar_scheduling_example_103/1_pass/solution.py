from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, start_time, end_time):
    # Convert times to datetime objects
    start_time = datetime.strptime(start_time, "%H:%M")
    end_time = datetime.strptime(end_time, "%H:%M")
    
    # Initialize available time slots
    available_slots = []
    current_time = start_time
    
    while current_time + timedelta(minutes=meeting_duration) <= end_time:
        available_slots.append(current_time)
        current_time += timedelta(minutes=15)  # Check every 15 minutes for flexibility
    
    # Find common available time slot
    common_slots = set(available_slots)
    for person, blocks in participants.items():
        person_unavailable_slots = set()
        for block_start, block_end in blocks:
            block_start_dt = datetime.strptime(block_start, "%H:%M")
            block_end_dt = datetime.strptime(block_end, "%H:%M")
            slot = start_time
            while slot < end_time:
                if block_start_dt <= slot < block_end_dt:
                    person_unavailable_slots.add(slot)
                slot += timedelta(minutes=15)
        common_slots -= person_unavailable_slots
    
    # Return the first common slot found
    if common_slots:
        meeting_start = min(common_slots)
        meeting_end = meeting_start + timedelta(minutes=meeting_duration)
        return meeting_start.strftime("%H:%M"), meeting_end.strftime("%H:%M")
    else:
        return None

# Define participants' schedules
participants = {
    "Diane": [("9:30", "10:00"), ("14:30", "15:00")],
    "Jack": [("13:30", "14:00"), ("14:30", "15:00")],
    "Eugene": [("9:00", "10:00"), ("10:30", "11:30"), ("12:00", "14:30"), ("15:00", "16:30")],
    "Patricia": [("9:30", "10:30"), ("11:00", "12:00"), ("12:30", "14:00"), ("15:00", "16:30")]
}

# Meeting parameters
meeting_duration = 30  # in minutes
start_time = "9:00"
end_time = "17:00"
day_of_week = "Monday"

# Find and print the meeting time
meeting_start, meeting_end = find_meeting_time(participants, meeting_duration, start_time, end_time)
print(f"{meeting_start}:{meeting_end} {day_of_week}")