def find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes):
    # Convert work hours to minutes since midnight for easier calculation
    work_start = work_hours_start[0] * 60 + work_hours_start[1]
    work_end = work_hours_end[0] * 60 + work_hours_end[1]
    
    # Initialize the free slots for all participants
    free_slots = []
    
    # Generate busy slots for each participant and find their free slots
    for schedule in participants_schedules:
        busy_slots = []
        for busy in schedule:
            start = busy[0][0] * 60 + busy[0][1]
            end = busy[1][0] * 60 + busy[1][1]
            busy_slots.append((start, end))
        
        # Sort busy slots by start time
        busy_slots.sort()
        
        # Find free slots by checking gaps between busy slots and work hours
        free = []
        previous_end = work_start
        for busy_start, busy_end in busy_slots:
            if busy_start > previous_end:
                free.append((previous_end, busy_start))
            previous_end = max(previous_end, busy_end)
        if previous_end < work_end:
            free.append((previous_end, work_end))
        
        free_slots.append(free)
    
    # Find common free slots across all participants
    common_free_slots = free_slots[0]
    for participant_free in free_slots[1:]:
        new_common = []
        i = j = 0
        while i < len(common_free_slots) and j < len(participant_free):
            slot1 = common_free_slots[i]
            slot2 = participant_free[j]
            # Find overlap between slot1 and slot2
            overlap_start = max(slot1[0], slot2[0])
            overlap_end = min(slot1[1], slot2[1])
            if overlap_start < overlap_end:
                new_common.append((overlap_start, overlap_end))
            # Move the pointer which ends first
            if slot1[1] < slot2[1]:
                i += 1
            else:
                j += 1
        common_free_slots = new_common
    
    # Find the first common free slot that can fit the meeting duration
    for slot in common_free_slots:
        if slot[1] - slot[0] >= duration_minutes:
            # Convert back to HH:MM format
            start_hh = slot[0] // 60
            start_mm = slot[0] % 60
            end_hh = (slot[0] + duration_minutes) // 60
            end_mm = (slot[0] + duration_minutes) % 60
            return f"{day}: {start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
    
    return "No suitable time found."

# Define the participants' schedules in the format [((HH, MM), (HH, MM)), ...]
participants_schedules = [
    [((13, 30), (14, 00)), ((14, 30), (15, 00))],  # Jacob
    [((9, 30), (10, 00)), ((11, 30), (12, 00)), ((13, 00), (13, 30)), ((16, 00), (16, 30))],  # Diana
    [((9, 30), (10, 30)), ((11, 00), (12, 30)), ((15, 30), (16, 00))],  # Adam
    [((9, 30), (10, 00)), ((10, 30), (12, 00)), ((13, 00), (15, 30)), ((16, 00), (16, 30))],  # Angela
    [((9, 00), (9, 30)), ((10, 30), (11, 30)), ((13, 00), (15, 00)), ((16, 30), (17, 00))],  # Dennis
]

# Define meeting parameters
day = "Monday"
work_hours_start = (9, 0)  # 9:00
work_hours_end = (17, 0)    # 17:00
duration_minutes = 30

# Find and print the meeting time
print(find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes))