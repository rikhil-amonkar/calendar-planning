def find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes):
    # Convert work hours to minutes since midnight for easier calculation
    work_start = work_hours_start[0] * 60 + work_hours_start[1]
    work_end = work_hours_end[0] * 60 + work_hours_end[1]
    
    # Initialize the free slots for all participants
    free_slots = []
    for schedule in participants_schedules:
        # Start with the entire work day as free
        free = [(work_start, work_end)]
        
        # Subtract the busy times from the free slots
        for busy_start, busy_end in schedule:
            busy_start_min = busy_start[0] * 60 + busy_start[1]
            busy_end_min = busy_end[0] * 60 + busy_end[1]
            new_free = []
            for slot_start, slot_end in free:
                if busy_end_min <= slot_start or busy_start_min >= slot_end:
                    # No overlap, keep the slot as is
                    new_free.append((slot_start, slot_end))
                else:
                    # Overlap, split the slot
                    if slot_start < busy_start_min:
                        new_free.append((slot_start, busy_start_min))
                    if busy_end_min < slot_end:
                        new_free.append((busy_end_min, slot_end))
            free = new_free
        free_slots.append(free)
    
    # Find the intersection of all free slots
    common_free = free_slots[0]
    for free in free_slots[1:]:
        new_common_free = []
        i = j = 0
        while i < len(common_free) and j < len(free):
            slot1_start, slot1_end = common_free[i]
            slot2_start, slot2_end = free[j]
            
            # Find the overlap between the two slots
            overlap_start = max(slot1_start, slot2_start)
            overlap_end = min(slot1_end, slot2_end)
            
            if overlap_start < overlap_end:
                new_common_free.append((overlap_start, overlap_end))
            
            # Move the pointer which ends first
            if slot1_end < slot2_end:
                i += 1
            else:
                j += 1
        common_free = new_common_free
    
    # Find the first slot that can fit the meeting duration
    for slot_start, slot_end in common_free:
        if slot_end - slot_start >= duration_minutes:
            meeting_start = slot_start
            meeting_end = meeting_start + duration_minutes
            # Convert back to HH:MM format
            start_hh = meeting_start // 60
            start_mm = meeting_start % 60
            end_hh = meeting_end // 60
            end_mm = meeting_end % 60
            return (f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}", day)
    
    return None

# Define the participants' schedules in HH:MM format
participants_schedules = [
    # Ronald's schedule (wide open)
    [],
    # Stephen's schedule
    [((10, 0), (10, 30)), ((12, 0), (12, 30))],
    # Brittany's schedule
    [((11, 0), (11, 30)), ((13, 30), (14, 0)), ((15, 30), (16, 0)), ((16, 30), (17, 0))],
    # Dorothy's schedule
    [((9, 0), (9, 30)), ((10, 0), (10, 30)), ((11, 0), (12, 30)), ((13, 0), (15, 0)), ((15, 30), (17, 0))],
    # Rebecca's schedule
    [((9, 30), (10, 30)), ((11, 0), (11, 30)), ((12, 0), (12, 30)), ((13, 0), (17, 0))],
    # Jordan's schedule
    [((9, 0), (9, 30)), ((10, 0), (11, 0)), ((11, 30), (12, 0)), ((13, 0), (15, 0)), ((15, 30), (16, 30))],
]

# Define the meeting parameters
day = "Monday"
work_hours_start = (9, 0)  # 9:00
work_hours_end = (17, 0)    # 17:00
duration_minutes = 30

# Find the meeting time
result = find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes)
if result:
    time_range, day = result
    print(f"{{{time_range}}} {day}")
else:
    print("No suitable time found.")