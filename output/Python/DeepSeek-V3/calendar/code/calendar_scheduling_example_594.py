def find_meeting_time(participants_busy, work_hours, duration, day):
    # Convert time strings to minutes since start of day for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    start_work, end_work = work_hours
    start_work_min = time_to_minutes(start_work)
    end_work_min = time_to_minutes(end_work)
    duration_min = duration * 60
    
    # Collect all busy intervals for all participants
    all_busy = []
    for busy_slots in participents_busy.values():
        for slot in busy_slots:
            start, end = slot
            all_busy.append((time_to_minutes(start), time_to_minutes(end)))
    
    # Sort all busy intervals by start time
    all_busy.sort()
    
    # Find free slots by checking gaps between busy intervals and work hours
    free_slots = []
    prev_end = start_work_min
    
    for start, end in all_busy:
        if start > prev_end:
            free_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    # Check the slot after last busy interval until end of work day
    if prev_end < end_work_min:
        free_slots.append((prev_end, end_work_min))
    
    # Find the first free slot that can accommodate the meeting duration
    for slot_start, slot_end in free_slots:
        if slot_end - slot_start >= duration_min:
            meeting_start = slot_start
            meeting_end = meeting_start + duration_min
            return (f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}", day)
    
    return None

# Define the task parameters
participants_busy = {
    'Adam': [('09:30', '10:00'), ('12:30', '13:00'), ('14:30', '15:00'), ('16:30', '17:00')],
    'Roy': [('10:00', '11:00'), ('11:30', '13:00'), ('13:30', '14:30'), ('16:30', '17:00')],
}
work_hours = ('09:00', '17:00')
meeting_duration = 30  # minutes
day = 'Monday'

# Find the meeting time
result = find_meeting_time(participants_busy, work_hours, meeting_duration, day)
if result:
    time_range, day = result
    print(f"{time_range}:{day}")
else:
    print("No suitable time found.")