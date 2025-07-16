from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration):
    # Convert times to datetime objects for easier comparison
    start_of_day = datetime.strptime("09:00", "%H:%M")
    end_of_day = datetime.strptime("17:00", "%H:%M")
    
    # Initialize available time slots as the full day
    available_slots = [(start_of_day, end_of_day)]
    
    # Process each participant's schedule
    for person, blocks in participants.items():
        new_slots = []
        for start, end in available_slots:
            for block in blocks:
                block_start = datetime.strptime(block[0], "%H:%M")
                block_end = datetime.strptime(block[1], "%H:%M")
                
                # If the current slot is before the block, keep it
                if end <= block_start:
                    new_slots.append((start, end))
                # If the current slot is after the block, keep it
                elif start >= block_end:
                    new_slots.append((start, end))
                # If the current slot overlaps with the block, split it
                else:
                    if start < block_start:
                        new_slots.append((start, block_start))
                    if end > block_end:
                        new_slots.append((block_end, end))
        
        available_slots = new_slots
    
    # Find a slot that fits the meeting duration
    for start, end in available_slots:
        if (end - start) >= timedelta(minutes=meeting_duration):
            return start.strftime("%H:%M"), end.strftime("%H:%M"), "Monday"
    
    return None

# Participants' schedules
participants = {
    "Stephen": [["10:00", "10:30"]],
    "Brittany": [["11:00", "11:30"]],
    "Dorothy": [["9:00", "9:30"]],
    "Rebecca": [["9:30", "10:30"]],
    "Jordan": [["9:00", "9:30"]]
}

# Meeting duration in minutes
meeting_duration = 30

# Find and print the meeting time
meeting_start, meeting_end, day = find_meeting_time(participants, meeting_duration)
print(f"{meeting_start}:{meeting_end}:{day}")