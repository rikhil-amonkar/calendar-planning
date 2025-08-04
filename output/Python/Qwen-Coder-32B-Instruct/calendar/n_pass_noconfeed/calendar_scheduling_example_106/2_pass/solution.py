from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, start_time, end_time):
    # Convert times to datetime objects for easier manipulation
    start = datetime.strptime(start_time, "%H:%M")
    end = datetime.strptime(end_time, "%H:%M")
    
    # Initialize available time slots
    available_slots = set()
    current = start
    
    # Populate the initial available slots
    while current + timedelta(hours=meeting_duration) <= end:
        available_slots.add(current.time())
        current += timedelta(minutes=30)  # Check every 30 minutes for precision
    
    # Filter out unavailable slots based on participants' schedules
    for person, blocks in participants.items():
        for block_start, block_end in blocks:
            block_start_dt = datetime.strptime(block_start, "%H:%M")
            block_end_dt = datetime.strptime(block_end, "%H:%M")
            
            current_slot = start
            while current_slot + timedelta(hours=meeting_duration) <= end:
                # Combine today's date with the current slot time
                current_slot_datetime = datetime.combine(datetime.today(), current_slot.time())
                if block_start_dt <= current_slot_datetime < block_end_dt:
                    available_slots.discard(current_slot.time())
                current_slot += timedelta(minutes=30)
    
    # Find the first available slot that fits the meeting duration
    for slot in available_slots:
        end_slot = (datetime.combine(datetime.today(), slot) + timedelta(hours=meeting_duration)).time()
        if end_slot <= end.time():
            return f"{slot.strftime('%H:%M')}-{end_slot.strftime('%H:%M')}", "Monday"
    
    return None, None

# Define participants' schedules
participants = {
    "Olivia": [("12:30", "13:30"), ("14:30", "15:00"), ("16:30", "17:00")],
    "Anna": [],
    "Virginia": [("9:00", "10:00"), ("11:30", "16:00"), ("16:30", "17:00")],
    "Paul": [("9:00", "9:30"), ("11:00", "11:30"), ("13:00", "14:00"), ("14:30", "16:00"), ("16:30", "17:00")]
}

# Meeting parameters
meeting_duration = 1  # in hours
start_time = "9:00"
end_time = "17:00"

# Find and print the meeting time
meeting_time, day_of_week = find_meeting_time(participants, meeting_duration, start_time, end_time)
print(f"{meeting_time}, {day_of_week}")