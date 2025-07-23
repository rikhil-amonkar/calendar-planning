def find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes):
    # Convert work hours to minutes since midnight for easier calculation
    work_start = work_hours_start[0] * 60 + work_hours_start[1]
    work_end = work_hours_end[0] * 60 + work_hours_end[1]
    
    # Initialize a list to keep track of busy intervals for all participants
    busy_intervals = []
    
    for schedule in participans_schedules:
        for interval in schedule:
            start_h, start_m = interval[0]
            end_h, end_m = interval[1]
            start = start_h * 60 + start_m
            end = end_h * 60 + end_m
            busy_intervals.append((start, end))
    
    # Sort all busy intervals by start time
    busy_intervals.sort()
    
    # Merge overlapping or adjacent busy intervals
    merged = []
    for start, end in busy_intervals:
        if not merged:
            merged.append([start, end])
        else:
            last_start, last_end = merged[-1]
            if start <= last_end:
                # Overlapping or adjacent intervals, merge them
                new_start = last_start
                new_end = max(last_end, end)
                merged[-1] = [new_start, new_end]
            else:
                merged.append([start, end])
    
    # Find available slots by checking gaps between busy intervals and work hours
    available_slots = []
    prev_end = work_start
    
    for start, end in merged:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    # Check the slot after last busy interval till work end
    if prev_end < work_end:
        available_slots.append((prev_end, work_end))
    
    # Check each available slot for sufficient duration
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= duration_minutes:
            # Found a suitable slot, convert back to HH:MM format
            start_h = slot_start // 60
            start_m = slot_start % 60
            end_h = (slot_start + duration_minutes) // 60
            end_m = (slot_start + duration_minutes) % 60
            return (f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}", day)
    
    return None

# Define work hours (9:00 to 17:00)
work_hours_start = (9, 0)
work_hours_end = (17, 0)

# Define meeting duration (30 minutes)
duration = 30

# Define participants' schedules as lists of time intervals in HH:MM format
joe_schedule = [((9, 30), (10, 0)), ((10, 30), (11, 0))]
keith_schedule = [((11, 30), (12, 0)), ((15, 0), (15, 30))]
patricia_schedule = [((9, 0), (9, 30)), ((13, 0), (13, 30))]
nancy_schedule = [((9, 0), (11, 0)), ((11, 30), (16, 30))]
pamela_schedule = [
    ((9, 0), (10, 0)),
    ((10, 30), (11, 0)),
    ((11, 30), (12, 30)),
    ((13, 0), (14, 0)),
    ((14, 30), (15, 0)),
    ((15, 30), (16, 0)),
    ((16, 30), (17, 0))
]

# Combine all schedules
participants_schedules = [
    joe_schedule,
    keith_schedule,
    patricia_schedule,
    nancy_schedule,
    pamela_schedule
]

# Find the meeting time
result = find_meeting_time(participants_schedules, "Monday", work_hours_start, work_hours_end, duration)

if result:
    time_range, day = result
    print(f"{{{time_range}}} {day}")
else:
    print("No suitable time found.")