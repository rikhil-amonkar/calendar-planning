def find_meeting_time(participants_schedules, duration_minutes, work_hours, day, constraints=None):
    if constraints is None:
        constraints = {}
    
    # Convert work hours to minutes since midnight
    work_start = work_hours[0]
    work_end = work_hours[1]
    work_start_min = work_start[0] * 60 + work_start[1]
    work_end_min = work_end[0] * 60 + work_end[1]
    
    # Initialize the free slots for all participants
    free_slots = []
    for participant, busy_slots in participants_schedules.items():
        # Convert busy slots to minutes since midnight
        busy_minutes = []
        for slot in busy_slots:
            start = slot[0][0] * 60 + slot[0][1]
            end = slot[1][0] * 60 + slot[1][1]
            busy_minutes.append((start, end))
        
        # Sort busy slots by start time
        busy_minutes.sort()
        
        # Find free slots for the participant
        participant_free = []
        prev_end = work_start_min
        for busy_start, busy_end in busy_minutes:
            if busy_start > prev_end:
                participant_free.append((prev_end, busy_start))
            prev_end = max(prev_end, busy_end)
        if prev_end < work_end_min:
            participant_free.append((prev_end, work_end_min))
        
        free_slots.append(participant_free)
    
    # Find intersection of all free slots
    common_free = free_slots[0]
    for participant_free in free_slots[1:]:
        new_common_free = []
        i = j = 0
        while i < len(common_free) and j < len(participant_free):
            start1, end1 = common_free[i]
            start2, end2 = participant_free[j]
            
            # Find overlap
            overlap_start = max(start1, start2)
            overlap_end = min(end1, end2)
            
            if overlap_start < overlap_end:
                new_common_free.append((overlap_start, overlap_end))
            
            # Move the pointer which ends first
            if end1 < end2:
                i += 1
            else:
                j += 1
        common_free = new_common_free
    
    # Apply constraints
    if constraints:
        for constraint in constraints.items():
            participant, constraint_slots = constraint
            constraint_minutes = []
            for slot in constraint_slots:
                start = slot[0][0] * 60 + slot[0][1]
                end = slot[1][0] * 60 + slot[1][1]
                constraint_minutes.append((start, end))
            
            # Remove slots that conflict with constraints
            new_common_free = []
            for slot in common_free:
                slot_start, slot_end = slot
                valid = True
                for constr_start, constr_end in constraint_minutes:
                    if not (slot_end <= constr_start or slot_start >= constr_end):
                        valid = False
                        break
                if valid:
                    new_common_free.append(slot)
            common_free = new_common_free
    
    # Find the first slot that can fit the meeting duration
    for slot in common_free:
        slot_start, slot_end = slot
        if slot_end - slot_start >= duration_minutes:
            # Convert back to HH:MM format
            start_hh = slot_start // 60
            start_mm = slot_start % 60
            end_hh = (slot_start + duration_minutes) // 60
            end_mm = (slot_start + duration_minutes) % 60
            return (f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}", day)
    
    return None

# Define the participants' schedules
participants_schedules = {
    'Natalie': [],
    'David': [((11, 30), (12, 00)), ((14, 30), (15, 00))],
    'Douglas': [((9, 30), (10, 00)), ((11, 30), (12, 00)), ((13, 00), (13, 30)), ((14, 30), (15, 00))],
    'Ralph': [((9, 00), (9, 30)), ((10, 00), (11, 00)), ((11, 30), (12, 30)), ((13, 30), (15, 00)), ((15, 30), (16, 00)), ((16, 30), (17, 00))],
    'Jordan': [((9, 00), (10, 00)), ((12, 00), (12, 30)), ((13, 00), (13, 30)), ((14, 30), (15, 00)), ((15, 30), (17, 00))]
}

# Define constraints (David doesn't want to meet before 14:00)
constraints = {
    'David': [((0, 00), (14, 00))]
}

# Define work hours (9:00 to 17:00)
work_hours = ((9, 00), (17, 00))

# Duration is 30 minutes
duration = 30

# Day is Monday
day = "Monday"

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, duration, work_hours, day, constraints)

if meeting_time:
    time_range, day = meeting_time
    print(f"{{{time_range}}} {day}")
else:
    print("No suitable time found.")