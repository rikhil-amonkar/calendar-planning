def find_meeting_time(participants_schedules, duration, work_hours, preferences):
    # Parse work hours
    work_start, work_end = work_hours.split(' to ')
    work_start = int(work_start.split(':')[0]) * 60 + int(work_start.split(':')[1])
    work_end = int(work_end.split(':')[0]) * 60 + int(work_end.split(':')[1])
    
    # Initialize available slots for each participant
    available_slots = {}
    for participant in participants_schedules:
        # Start with the entire work day as available
        available = [(work_start, work_end)]
        # Subtract blocked times
        for block in participants_schedules[participant]:
            start, end = block.split(' to ')
            start = int(start.split(':')[0]) * 60 + int(start.split(':')[1])
            end = int(end.split(':')[0]) * 60 + int(end.split(':')[1])
            new_available = []
            for slot in available:
                if slot[1] <= start or slot[0] >= end:
                    new_available.append(slot)
                else:
                    if slot[0] < start:
                        new_available.append((slot[0], start))
                    if slot[1] > end:
                        new_available.append((end, slot[1]))
            available = new_available
        available_slots[participant] = available
    
    # Apply Helen's preference (no meetings after 13:30)
    if 'Helen' in preferences:
        pref_start, pref_end = preferences['Helen'].split(' to ')
        pref_end = int(pref_end.split(':')[0]) * 60 + int(pref_end.split(':')[1])
        new_available = []
        for slot in available_slots['Helen']:
            if slot[0] >= pref_end:
                continue
            if slot[1] > pref_end:
                new_available.append((slot[0], pref_end))
            else:
                new_available.append(slot)
        available_slots['Helen'] = new_available
    
    # Find overlapping slots
    common_slots = []
    # Start with Helen's slots (as she has the most constraints)
    for helen_slot in available_slots['Helen']:
        # Check if Margaret and Donna are available during this slot
        for margaret_slot in available_slots['Margaret']:
            if margaret_slot[0] >= helen_slot[1] or margaret_slot[1] <= helen_slot[0]:
                continue
            margaret_overlap = (max(helen_slot[0], margaret_slot[0]), min(helen_slot[1], margaret_slot[1]))
            for donna_slot in available_slots['Donna']:
                if donna_slot[0] >= margaret_overlap[1] or donna_slot[1] <= margaret_overlap[0]:
                    continue
                donna_overlap = (max(margaret_overlap[0], donna_slot[0]), min(margaret_overlap[1], donna_slot[1]))
                if donna_overlap[1] - donna_overlap[0] >= duration:
                    common_slots.append(donna_overlap)
    
    # Select the first available slot that fits the duration
    for slot in common_slots:
        if slot[1] - slot[0] >= duration:
            # Convert back to HH:MM format
            start_hh = slot[0] // 60
            start_mm = slot[0] % 60
            end_hh = (slot[0] + duration) // 60
            end_mm = (slot[0] + duration) % 60
            return f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
    
    return None

# Input data
participants_schedules = {
    'Margaret': ['9:00 to 10:00', '10:30 to 11:00', '11:30 to 12:00', '13:00 to 13:30', '15:00 to 15:30'],
    'Donna': ['14:30 to 15:00', '16:00 to 16:30'],
    'Helen': ['9:00 to 9:30', '10:00 to 11:30', '13:00 to 14:00', '14:30 to 15:00', '15:30 to 17:00']
}
duration = 30  # minutes
work_hours = '9:00 to 17:00'
preferences = {'Helen': '9:00 to 13:30'}

# Find meeting time
meeting_time = find_meeting_time(participants_schedules, duration, work_hours, preferences)
print(f"Monday:{meeting_time}")