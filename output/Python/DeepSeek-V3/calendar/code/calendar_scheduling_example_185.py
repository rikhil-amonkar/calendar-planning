def find_meeting_time(participants_schedules, duration, work_hours, preferences):
    # Parse work hours
    work_start, work_end = work_hours.split(' to ')
    work_start = int(work_start.split(':')[0])
    work_end = int(work_end.split(':')[0])
    
    # Initialize available slots (in minutes since 9:00)
    slots = []
    current_time = work_start * 60
    
    while current_time + duration <= work_end * 60:
        slots.append((current_time, current_time + duration))
        current_time += 30  # Assuming 30-minute increments for simplicity
    
    # Apply Megan's preference to avoid meetings before 10:00
    preferred_start = 10 * 60  # 10:00 in minutes
    slots = [slot for slot in slots if slot[0] >= preferred_start]
    
    # Check each slot against each participant's busy times
    for slot_start, slot_end in slots:
        slot_ok = True
        for participant, meetings in participants_schedules.items():
            for meeting in meetings:
                meeting_start, meeting_end = meeting.split(' to ')
                meeting_start = int(meeting_start.split(':')[0]) * 60 + int(meeting_start.split(':')[1])
                meeting_end = int(meeting_end.split(':')[0]) * 60 + int(meeting_end.split(':')[1])
                
                # Check if slot overlaps with any meeting
                if not (slot_end <= meeting_start or slot_start >= meeting_end):
                    slot_ok = False
                    break
            if not slot_ok:
                break
        
        if slot_ok:
            # Convert slot back to HH:MM format
            start_hh = slot_start // 60
            start_mm = slot_start % 60
            end_hh = slot_end // 60
            end_mm = slot_end % 60
            return f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
    
    return None

# Define participants' schedules
participants_schedules = {
    'Kimberly': ['10:00 to 10:30', '11:00 to 12:00', '16:00 to 16:30'],
    'Megan': [],
    'Marie': ['10:00 to 11:00', '11:30 to 15:00', '16:00 to 16:30'],
    'Diana': ['9:30 to 10:00', '10:30 to 14:30', '15:30 to 17:00']
}

# Meeting details
duration = 30  # minutes
work_hours = '9:00 to 17:00'
preferences = {'Megan': 'avoid before 10:00'}

# Find meeting time
meeting_time = find_meeting_time(participants_schedules, duration, work_hours, preferences)

# Output the result
print(f"{meeting_time}:Monday")