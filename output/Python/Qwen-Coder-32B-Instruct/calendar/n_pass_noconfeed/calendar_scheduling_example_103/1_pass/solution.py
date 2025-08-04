from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, start_time, end_time):
    # Convert start and end times to datetime objects
    start_time = datetime.strptime(start_time, "%H:%M")
    end_time = datetime.strptime(end_time, "%H:%M")
    
    # Initialize available time slots
    available_slots = []
    
    # Iterate over each minute in the workday
    current_time = start_time
    while current_time + timedelta(minutes=meeting_duration) <= end_time:
        # Check if the current slot is available for all participants
        slot_available = True
        for person, blocks in participants.items():
            for block_start, block_end in blocks:
                block_start_time = datetime.strptime(block_start, "%H:%M")
                block_end_time = datetime.strptime(block_end, "%H:%M")
                if block_start_time <= current_time < block_end_time or \
                   block_start_time < current_time + timedelta(minutes=meeting_duration) <= block_end_time:
                    slot_available = False
                    break
            if not slot_available:
                break
        
        # If the slot is available for all, add it to the list
        if slot_available:
            available_slots.append((current_time, current_time + timedelta(minutes=meeting_duration)))
        
        # Move to the next minute
        current_time += timedelta(minutes=1)
    
    # Return the first available slot
    if available_slots:
        start, end = available_slots[0]
        return f"{start.strftime('%H:%M')}:{end.strftime('%H:%M')}, Monday"
    else:
        return "No available time slot found"

# Define participants' schedules
participants = {
    "Diane": [("9:30", "10:00"), ("14:30", "15:00")],
    "Jack": [("13:30", "14:00"), ("14:30", "15:00")],
    "Eugene": [("9:00", "10:00"), ("10:30", "11:30"), ("12:00", "14:30"), ("15:00", "16:30")],
    "Patricia": [("9:30", "10:30"), ("11:00", "12:00"), ("12:30", "14:00"), ("15:00", "16:30")]
}

# Meeting duration in minutes
meeting_duration = 30

# Workday start and end times
start_time = "9:00"
end_time = "17:00"

# Find and print the meeting time
print(find_meeting_time(participants, meeting_duration, start_time, end_time))