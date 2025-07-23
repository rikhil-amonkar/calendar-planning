def find_meeting_time(participants_schedules, duration_minutes, work_hours_start, work_hours_end, day):
    # Convert work hours to minutes since midnight for easier calculation
    start_time = work_hours_start * 60
    end_time = work_hours_end * 60
    
    # Initialize a list to keep track of busy intervals for all participants
    busy_intervals = []
    
    # Collect all busy intervals from each participant
    for schedule in participants_schedules:
        for busy_start, busy_end in schedule:
            busy_intervals.append((busy_start * 60, busy_end * 60))
    
    # Sort the busy intervals by start time
    busy_intervals.sort()
    
    # Merge overlapping or adjacent busy intervals
    merged_intervals = []
    for interval in busy_intervals:
        if not merged_intervals:
            merged_intervals.append(interval)
        else:
            last_start, last_end = merged_intervals[-1]
            current_start, current_end = interval
            if current_start <= last_end:
                # Overlapping or adjacent intervals, merge them
                new_start = last_start
                new_end = max(last_end, current_end)
                merged_intervals[-1] = (new_start, new_end)
            else:
                merged_intervals.append(interval)
    
    # Find available slots between merged busy intervals
    available_slots = []
    previous_end = start_time
    
    for interval in merged_intervals:
        current_start, current_end = interval
        if current_start > previous_end:
            # There's a gap between previous_end and current_start
            available_slots.append((previous_end, current_start))
        previous_end = max(previous_end, current_end)
    
    # Check the slot after the last busy interval
    if previous_end < end_time:
        available_slots.append((previous_end, end_time))
    
    # Find the first available slot that can fit the meeting duration
    for slot in available_slots:
        slot_start, slot_end = slot
        if slot_end - slot_start >= duration_minutes:
            meeting_start = slot_start
            meeting_end = meeting_start + duration_minutes
            # Convert back to hours and minutes and ensure they are integers
            start_hh = int(meeting_start // 60)
            start_mm = int(meeting_start % 60)
            end_hh = int(meeting_end // 60)
            end_mm = int(meeting_end % 60)
            return (start_hh, start_mm, end_hh, end_mm)
    
    return None

# Define the participants' schedules in hours (converted to float for simplicity)
jacqueline_schedule = [
    (9.0, 9.5), (11.0, 11.5), (12.5, 13.0), (15.5, 16.0)
]
harold_schedule = [
    (10.0, 10.5), (13.0, 13.5), (15.0, 17.0)
]
arthur_schedule = [
    (9.0, 9.5), (10.0, 12.5), (14.5, 15.0), (15.5, 17.0)
]
kelly_schedule = [
    (9.0, 9.5), (10.0, 11.0), (11.5, 12.5), (14.0, 15.0), (15.5, 16.0)
]

# Harold doesn't want to meet after 13:00, so add his constraint
harold_constraint = (13.0, 17.0)
harold_schedule.append(harold_constraint)

# Combine all schedules
participants_schedules = [
    jacqueline_schedule,
    harold_schedule,
    arthur_schedule,
    kelly_schedule
]

# Meeting duration in minutes (30 minutes)
duration = 30

# Work hours (9:00 to 17:00)
work_start = 9
work_end = 17

# Day of the week
day_of_week = "Monday"

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, duration, work_start, work_end, day_of_week)

if meeting_time:
    start_hh, start_mm, end_hh, end_mm = meeting_time
    # Format the output as HH:MM:HH:MM
    print(f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}")
    print(day_of_week)
else:
    print("No suitable meeting time found.")