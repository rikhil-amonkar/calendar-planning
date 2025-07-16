def find_meeting_time(participants_schedules, days, work_hours_start, work_hours_end, duration_minutes):
    # Convert work hours to minutes since midnight for easier calculation
    work_start = work_hours_start * 60
    work_end = work_hours_end * 60
    
    # Iterate through each day to find the earliest available slot
    for day in days:
        # Initialize the available slots for the day
        available_slots = []
        current_start = work_start
        
        # Collect all busy slots for the day for all participants
        busy_slots = []
        for participant in participants_schedules:
            if day in participant:
                busy_slots.extend(participant[day])
        
        # If no busy slots, the whole day is available
        if not busy_slots:
            if work_end - work_start >= duration_minutes:
                start_hh = work_start // 60
                start_mm = work_start % 60
                end_hh = (work_start + duration_minutes) // 60
                end_mm = (work_start + duration_minutes) % 60
                return day, f"{start_hh:02d}:{start_mm:02d}-{end_hh:02d}:{end_mm:02d}"
            continue
        
        # Sort busy slots by start time
        busy_slots.sort(key=lambda x: x[0])
        
        # Find available slots by checking gaps between busy slots
        for busy_start, busy_end in busy_slots:
            if busy_start > current_start:
                available_slots.append((current_start, busy_start))
            current_start = max(current_start, busy_end)
        
        # Check the slot after the last busy slot
        if current_start < work_end:
            available_slots.append((current_start, work_end))
        
        # Check each available slot for sufficient duration
        for slot_start, slot_end in available_slots:
            if slot_end - slot_start >= duration_minutes:
                # Convert back to HH:MM format
                start_hh = slot_start // 60
                start_mm = slot_start % 60
                end_hh = (slot_start + duration_minutes) // 60
                end_mm = (slot_start + duration_minutes) % 60
                
                return day, f"{start_hh:02d}:{start_mm:02d}-{end_hh:02d}:{end_mm:02d}"
    
    return None, None

# Define the participants' schedules
mary_schedule = {
    "Tuesday": [(10 * 60, 10 * 60 + 30), (15 * 60 + 30, 16 * 60)],
    "Wednesday": [(9 * 60 + 30, 10 * 60), (15 * 60, 15 * 60 + 30)],
    "Thursday": [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60 + 30)],
}

alexis_schedule = {
    "Monday": [(9 * 60, 10 * 60), (10 * 60 + 30, 12 * 60), (12 * 60 + 30, 16 * 60 + 30)],
    "Tuesday": [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60 + 30), (12 * 60, 15 * 60 + 30), (16 * 60, 17 * 60)],
    "Wednesday": [(9 * 60, 11 * 60), (11 * 60 + 30, 17 * 60)],
    "Thursday": [(10 * 60, 12 * 60), (14 * 60, 14 * 60 + 30), (15 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)],
}

# Define the parameters
days_to_check = ["Monday", "Tuesday", "Wednesday", "Thursday"]
work_hours_start = 9
work_hours_end = 17
meeting_duration = 30

# Find the meeting time
day, time_slot = find_meeting_time([mary_schedule, alexis_schedule], days_to_check, work_hours_start, work_hours_end, meeting_duration)

# Output the result
if day and time_slot:
    print(f"First available meeting slot: {day}, {time_slot}")
else:
    print("No available meeting slot found in the given constraints")