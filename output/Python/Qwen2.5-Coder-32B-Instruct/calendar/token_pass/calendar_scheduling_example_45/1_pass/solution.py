def time_to_minutes(time_str):
    """Converts time in HH:MM format to minutes since midnight."""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Converts minutes since midnight back to HH:MM format."""
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02}:{minutes:02}"

def get_available_slots(start, end, blocks):
    """Generates a list of available time slots given start, end, and blocked times."""
    available_slots = []
    current_start = start
    
    for block in blocks:
        block_start, block_end = block
        if current_start < block_start:
            available_slots.append((current_start, block_start))
        current_start = max(current_start, block_end)
    
    if current_start < end:
        available_slots.append((current_start, end))
    
    return available_slots

# Define the work hours in minutes since midnight
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")

# Define the meeting duration in minutes
meeting_duration = 30

# Define the blocked times for each participant
samuel_blocks = [
    (time_to_minutes("09:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:00"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00")),
]

# Generate available slots for each participant
andrew_slots = [(work_start, work_end)]
grace_slots = [(work_start, work_end)]
samuel_slots = get_available_slots(work_start, work_end, samuel_blocks)

# Function to find the first common slot
def find_first_common_slot(slots1, slots2, slots3, duration):
    for slot1 in slots1:
        for slot2 in slots2:
            for slot3 in slots3:
                # Find the intersection of the three slots
                start = max(slot1[0], slot2[0], slot3[0])
                end = min(slot1[1], slot2[1], slot3[1])
                
                if end - start >= duration:
                    return start, start + duration
    return None

# Find the first common slot that fits the meeting duration
common_slot = find_first_common_slot(andrew_slots, grace_slots, samuel_slots, meeting_duration)

# Output the result
if common_slot:
    start_time = minutes_to_time(common_slot[0])
    end_time = minutes_to_time(common_slot[1])
    print(f"{start_time}:{end_time} Monday")
else:
    print("No common slot found")