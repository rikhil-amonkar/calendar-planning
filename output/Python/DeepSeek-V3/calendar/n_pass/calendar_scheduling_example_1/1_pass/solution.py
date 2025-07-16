def find_meeting_time(participants_schedules, preferences, duration_minutes, work_hours_start, work_hours_end):
    # Convert all time strings to minutes since midnight for easier calculations
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    
    # Collect all busy intervals for all participants
    busy_intervals = []
    for participant, schedules in participants_schedules.items():
        for interval in schedules:
            start, end = map(time_to_minutes, interval.split(' to '))
            busy_intervals.append((start, end))
    
    # Add preference constraints as busy intervals
    for participant, constraint in preferences.items():
        if constraint == "avoid after 15:00":
            avoid_start = time_to_minutes("15:00")
            busy_intervals.append((avoid_start, work_end))
    
    # Sort all busy intervals by start time
    busy_intervals.sort()
    
    # Merge overlapping or adjacent busy intervals
    merged = []
    for start, end in busy_intervals:
        if not merged:
            merged.append((start, end))
        else:
            last_start, last_end = merged[-1]
            if start <= last_end:
                # Overlapping or adjacent, merge them
                new_start = min(last_start, start)
                new_end = max(last_end, end)
                merged[-1] = (new_start, new_end)
            else:
                merged.append((start, end))
    
    # Find available slots between work hours and busy intervals
    available_slots = []
    prev_end = work_start
    for start, end in merged:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        available_slots.append((prev_end, work_end))
    
    # Find the first available slot that can fit the meeting
    duration = duration_minutes
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= duration:
            meeting_start = slot_start
            meeting_end = meeting_start + duration
            return (minutes_to_time(meeting_start), minutes_to_time(meeting_end))
    
    return None

# Define participants' schedules
participants_schedules = {
    "Raymond": [
        "9:00 to 9:30",
        "11:30 to 12:00",
        "13:00 to 13:30",
        "15:00 to 15:30"
    ],
    "Billy": [
        "10:00 to 10:30",
        "12:00 to 13:00",
        "16:30 to 17:00"
    ],
    "Donald": [
        "9:00 to 9:30",
        "10:00 to 11:00",
        "12:00 to 13:00",
        "14:00 to 14:30",
        "16:00 to 17:00"
    ]
}

# Define preferences
preferences = {
    "Billy": "avoid after 15:00"
}

# Find meeting time
meeting_time = find_meeting_time(
    participants_schedules,
    preferences,
    30,  # duration in minutes
    "9:00",  # work hours start
    "17:00"   # work hours end
)

# Output the result
if meeting_time:
    start_time, end_time = meeting_time
    print(f"{{{start_time}:{end_time}}} Monday")
else:
    print("No suitable time found.")