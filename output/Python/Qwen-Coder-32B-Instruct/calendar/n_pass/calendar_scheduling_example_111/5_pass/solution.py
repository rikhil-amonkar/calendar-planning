from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, work_start, work_end):
    # Convert times to datetime objects for easier manipulation
    work_start = datetime.strptime(work_start, "%H:%M")
    work_end = datetime.strptime(work_end, "%H:%M")
    
    # Initialize available time slots for each participant
    available_slots = {}
    for participant, blocks in participants.items():
        current_time = work_start
        available_slots[participant] = []
        for block in blocks:
            block_start, block_end = map(lambda x: datetime.strptime(x, "%H:%M"), block)
            if current_time < block_start:
                available_slots[participant].append((current_time, block_start))
            current_time = max(current_time, block_end)
        if current_time < work_end:
            available_slots[participant].append((current_time, work_end))
    
    # Find common available slots
    common_slots = []
    for slot in available_slots[next(iter(available_slots))]:
        start, end = slot
        if (end - start) >= timedelta(minutes=meeting_duration):
            is_common = True
            for participant, slots in available_slots.items():
                slot_found = False
                for s, e in slots:
                    overlap_start = max(start, s)
                    overlap_end = min(end, e)
                    if overlap_start < overlap_end and (overlap_end - overlap_start) >= timedelta(minutes=meeting_duration):
                        slot_found = True
                        break
                if not slot_found:
                    is_common = False
                    break
            if is_common:
                common_slots.append(slot)
    
    # Define the unavailable time slot
    unavailable_start = datetime.strptime("10:50", "%H:%M")
    unavailable_end = datetime.strptime("12:00", "%H:%M")
    
    # Filter out slots that conflict with the unavailable time (10:50 to 12:00)
    filtered_slots = [slot for slot in common_slots 
                      if not (unavailable_start <= slot[0] < unavailable_end) 
                      and not (unavailable_start < slot[1] <= unavailable_end)
                      and not (slot[0] < unavailable_start < slot[1])
                      and not (slot[0] < unavailable_end < slot[1])]
    
    # Return the first common slot found after filtering
    if filtered_slots:
        start_time, _ = filtered_slots[0]
        end_time = start_time + timedelta(minutes=meeting_duration)
        return f"{start_time.strftime('%H:%M')}-{end_time.strftime('%H:%M')}", "Monday"
    else:
        return None, None

# Participants' schedules
participants = {
    'Gregory': [('9:00', '10:00'), ('10:30', '11:30'), ('12:30', '13:00'), ('13:30', '14:00')],
    'Natalie': [],
    'Christine': [('9:00', '11:30'), ('13:30', '17:00')],
    'Vincent': [('9:00', '9:30'), ('10:30', '12:00'), ('12:30', '14:00'), ('14:30', '17:00')]
}

# Meeting duration in minutes
meeting_duration = 30

# Work hours
work_start = "9:00"
work_end = "17:00"

# Find and print the meeting time
meeting_time, day_of_week = find_meeting_time(participants, meeting_duration, work_start, work_end)
print(f"{meeting_time}, {day_of_week}")