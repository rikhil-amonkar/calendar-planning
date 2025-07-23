def find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes):
    # Convert work hours to minutes since midnight for easier calculation
    work_start = work_hours_start * 60
    work_end = work_hours_end * 60
    
    # Initialize the list of busy intervals for all participants
    all_busy_intervals = []
    
    for schedule in participants_schedules:
        for busy_start, busy_end in schedule:
            # Convert each busy interval to minutes since midnight
            start_min = busy_start[0] * 60 + busy_start[1]
            end_min = busy_end[0] * 60 + busy_end[1]
            all_busy_intervals.append((start_min, end_min))
    
    # Sort all busy intervals by start time
    all_busy_intervals.sort()
    
    # Merge overlapping or adjacent busy intervals
    merged_intervals = []
    for start, end in all_busy_intervals:
        if not merged_intervals:
            merged_intervals.append((start, end))
        else:
            last_start, last_end = merged_intervals[-1]
            if start <= last_end:
                # Overlapping or adjacent intervals, merge them
                new_start = min(last_start, start)
                new_end = max(last_end, end)
                merged_intervals[-1] = (new_start, new_end)
            else:
                merged_intervals.append((start, end))
    
    # Find available slots between work hours and busy intervals
    available_slots = []
    previous_end = work_start
    
    for start, end in merged_intervals:
        if start > previous_end:
            # There's a gap between previous_end and start
            available_slots.append((previous_end, start))
        previous_end = max(previous_end, end)
    
    # Check the slot after the last busy interval
    if previous_end < work_end:
        available_slots.append((previous_end, work_end))
    
    # Find the first available slot that can fit the meeting duration
    duration = duration_minutes
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= duration:
            # Found a suitable slot
            meeting_start = slot_start
            meeting_end = meeting_start + duration
            # Convert back to HH:MM format
            start_hh = meeting_start // 60
            start_mm = meeting_start % 60
            end_hh = meeting_end // 60
            end_mm = meeting_end % 60
            return (f"{start_hh:02d}:{start_mm:02d}-{end_hh:02d}:{end_mm:02d}", day)
    
    return None

# Define the participants' schedules in HH:MM format converted to tuples (HH, MM)
participants_schedules = [
    [],  # Andrea's calendar is wide open
    [(9, 0, 9, 30), (14, 0, 14, 30)],  # Jack
    [(9, 30, 10, 30), (13, 0, 14, 0), (15, 0, 15, 30), (16, 30, 17, 0)],  # Madison
    [(9, 30, 10, 30), (11, 0, 11, 30), (12, 0, 13, 30), (14, 30, 15, 30), (16, 0, 17, 0)],  # Rachel
    [(9, 0, 11, 30), (12, 0, 16, 30)],  # Douglas
    [(9, 0, 9, 30), (13, 0, 14, 0), (14, 30, 17, 0)],  # Ryan
]

# Convert the schedules to a list of busy intervals in (start, end) format
busy_intervals_per_participant = []
for schedule in participants_schedules:
    participant_busy = []
    for interval in schedule:
        start_hh, start_mm, end_hh, end_mm = interval
        participant_busy.append(((start_hh, start_mm), (end_hh, end_mm)))
    busy_intervals_per_participant.append(participant_busy)

# Find a meeting time
meeting_time = find_meeting_time(
    busy_intervals_per_participant,
    day="Monday",
    work_hours_start=9,
    work_hours_end=17,
    duration_minutes=30
)

# Output the result
if meeting_time:
    time_range, day = meeting_time
    print(f"{time_range} on {day}")
else:
    print("No suitable time found.")