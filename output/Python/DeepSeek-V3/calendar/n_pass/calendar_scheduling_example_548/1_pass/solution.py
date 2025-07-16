def find_meeting_time(participants_schedules, work_hours, day, duration, preferences):
    # Parse work hours
    work_start, work_end = work_hours.split(' to ')
    work_start = int(work_start.split(':')[0])
    work_end = int(work_end.split(':')[0])
    
    # Initialize free slots for the day
    free_slots = []
    
    # Generate all possible 30-minute slots within work hours
    for hour in range(work_start, work_end):
        for minute in [0, 30]:
            if hour == work_end - 1 and minute == 30:
                continue  # Skip slots that would end after work hours
            start_time = f"{hour:02d}:{minute:02d}"
            end_hour = hour + (minute + duration) // 60
            end_minute = (minute + duration) % 60
            end_time = f"{end_hour:02d}:{end_minute:02d}"
            free_slots.append((start_time, end_time))
    
    # Filter slots based on participants' schedules
    available_slots = []
    for slot in free_slots:
        start, end = slot
        # Check Judy's schedule (free all day)
        # Check Nicole's schedule
        nicole_busy = False
        for meeting in participants_schedules['Nicole']:
            meeting_start, meeting_end = meeting.split(' to ')
            # Check if current slot overlaps with Nicole's meeting
            if not (end <= meeting_start or start >= meeting_end):
                nicole_busy = True
                break
        
        # Check Nicole's preference (not before 16:00)
        if start < '16:00':
            nicole_busy = True
        
        if not nicole_busy:
            available_slots.append(slot)
    
    # Return the first available slot
    if available_slots:
        return available_slots[0]
    else:
        return None

# Define inputs
participants_schedules = {
    'Judy': [],
    'Nicole': ['9:00 to 10:00', '10:30 to 16:30']
}
work_hours = '9:00 to 17:00'
day = 'Monday'
duration = 30  # minutes
preferences = {'Nicole': 'not before 16:00'}

# Find meeting time
meeting_slot = find_meeting_time(participants_schedules, work_hours, day, duration, preferences)

# Output result
if meeting_slot:
    start, end = meeting_slot
    print(f"{day}:{start}:{end}")
else:
    print("No available slot found.")