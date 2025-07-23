def find_meeting_time(eric_busy, henry_busy, henry_preference, work_hours, duration):
    # Convert all time strings to minutes since 9:00 (work_hours start)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return (hh - 9) * 60 + mm  # 9:00 is 0 minutes
    
    def minutes_to_time(minutes):
        hh = 9 + (minutes // 60)
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start = time_to_minutes(work_hours[0])
    work_end = time_to_minutes(work_hours[1])
    duration_mins = duration * 60
    
    # Generate busy slots in minutes for Eric and Henry
    eric_slots = []
    for slot in eric_busy:
        start, end = map(time_to_minutes, slot.split(' to '))
        eric_slots.append((start, end))
    
    henry_slots = []
    for slot in henry_busy:
        start, end = map(time_to_minutes, slot.split(' to '))
        henry_slots.append((start, end))
    
    # Combine and sort all busy slots
    all_busy = eric_slots + henry_slots
    all_busy.sort()
    
    # Find free slots by checking gaps between busy slots and work hours
    free_slots = []
    prev_end = work_start
    
    for start, end in all_busy:
        if start > prev_end:
            free_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    if prev_end < work_end:
        free_slots.append((prev_end, work_end))
    
    # Filter free slots that meet duration and Henry's preference
    valid_slots = []
    for start, end in free_slots:
        if end - start >= duration_mins:
            slot_start_time = minutes_to_time(start)
            hh = int(slot_start_time.split(':')[0])
            # Henry prefers not after 10:00, so before 10:00 (which is 60 minutes)
            if henry_preference and start < 60:
                valid_slots.append((start, start + duration_mins))
            elif not henry_preference:
                valid_slots.append((start, start + duration_mins))
    
    if not valid_slots:
        return None
    
    # Pick the earliest possible slot
    chosen_start, chosen_end = valid_slots[0]
    return f"{minutes_to_time(chosen_start)}:{minutes_to_time(chosen_end)}"

# Input data
eric_busy = ["12:00 to 13:00", "14:00 to 15:00"]
henry_busy = ["9:30 to 10:00", "10:30 to 11:00", "11:30 to 12:30", "13:00 to 13:30", "14:30 to 15:00", "16:00 to 17:00"]
henry_preference = True  # Prefers not after 10:00
work_hours = ("9:00", "17:00")
duration = 0.5  # half hour

# Find meeting time
meeting_time = find_meeting_time(eric_busy, henry_busy, henry_preference, work_hours, duration)

if meeting_time:
    start, end = meeting_time.split(':')
    print(f"Monday {{{start}:{end}}}")
else:
    print("No suitable time found.")