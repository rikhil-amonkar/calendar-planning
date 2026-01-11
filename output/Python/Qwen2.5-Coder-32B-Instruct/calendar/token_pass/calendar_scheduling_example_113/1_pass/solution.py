def find_common_free_slot(participants, meeting_duration, work_start, work_end):
    from collections import defaultdict

    # Initialize free slots for each participant
    free_slots = defaultdict(list)
    
    # Define the workday in minutes from start to end
    work_start_minutes = work_start * 60
    work_end_minutes = work_end * 60
    
    # Populate free slots for each participant
    for name, blocks in participants.items():
        current_time = work_start_minutes
        for block in sorted(blocks):
            block_start, block_end = block[0] * 60, block[1] * 60
            if current_time < block_start:
                free_slots[name].append((current_time, block_start))
            current_time = max(current_time, block_end)
        if current_time < work_end_minutes:
            free_slots[name].append((current_time, work_end_minutes))
    
    # Find common free slots
    common_free_slots = free_slots[list(free_slots.keys())[0]]
    for name in list(free_slots.keys())[1:]:
        new_common_slots = []
        for slot1 in common_free_slots:
            for slot2 in free_slots[name]:
                overlap_start = max(slot1[0], slot2[0])
                overlap_end = min(slot1[1], slot2[1])
                if overlap_end - overlap_start >= meeting_duration:
                    new_common_slots.append((overlap_start, overlap_end))
        common_free_slots = new_common_slots
    
    # Convert the first valid slot back to HH:MM format
    if common_free_slots:
        start, end = common_free_slots[0]
        start_hour, start_minute = divmod(start, 60)
        end_hour, end_minute = divmod(end, 60)
        return f"{start_hour:02}:{start_minute:02}:{end_hour:02}:{end_minute:02} Monday"
    else:
        return "No common free slot found"

# Define participants' schedules
participants = {
    'Bradley': [(9.5, 10), (12.5, 13), (13.5, 14), (15.5, 16)],
    'Teresa': [(10.5, 11), (12, 12.5), (13, 13.5), (14.5, 15)],
    'Elizabeth': [(9, 9.5), (10.5, 11.5), (13, 13.5), (14.5, 15), (15.5, 17)],
    'Christian': [(9, 9.5), (10.5, 17)]
}

# Meeting duration in hours
meeting_duration = 0.5 * 60  # 30 minutes

# Workday start and end in hours
work_start = 9
work_end = 17

# Find and print the common free slot
print(find_common_free_slot(participants, meeting_duration, work_start, work_end))