def find_meeting_time(participants_schedules, duration_minutes=30, work_hours_start="09:00", work_hours_end="17:00"):
    # Convert time strings to minutes since midnight for easier calculations
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    
    # Collect all busy intervals for each participant
    all_busy_intervals = []
    for participant, constraints in participants_schedules.items():
        for interval in constraints.get('busy', []):
            start, end = map(time_to_minutes, interval.split(' to '))
            all_busy_intervals.append((start, end))
    
    # Add constraints as busy intervals
    for participant, constraints in participants_schedules.items():
        for constraint in constraints.get('constraints', []):
            if constraint.startswith('not after'):
                time_limit = time_to_minutes(constraint.split(' ')[-1])
                all_busy_intervals.append((time_limit, work_end))
    
    # Sort all busy intervals by start time
    all_busy_intervals.sort()
    
    # Merge overlapping or adjacent busy intervals
    merged_intervals = []
    for start, end in all_busy_intervals:
        if not merged_intervals:
            merged_intervals.append([start, end])
        else:
            last_start, last_end = merged_intervals[-1]
            if start <= last_end:
                merged_intervals[-1][1] = max(end, last_end)
            else:
                merged_intervals.append([start, end])
    
    # Find available slots by looking at gaps between busy intervals
    available_slots = []
    prev_end = work_start
    for start, end in merged_intervals:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        available_slots.append((prev_end, work_end))
    
    # Find the first available slot that can fit the meeting
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= duration_minutes:
            meeting_start = slot_start
            meeting_end = meeting_start + duration_minutes
            # Convert back to HH:MM format
            def minutes_to_time(minutes):
                hh = minutes // 60
                mm = minutes % 60
                return f"{hh:02d}:{mm:02d}"
            return minutes_to_time(meeting_start), minutes_to_time(meeting_end)
    
    return None, None

# Define participants' schedules and constraints
participants_schedules = {
    "Emily": {
        "busy": [
            "10:00 to 10:30",
            "11:30 to 12:30",
            "14:00 to 15:00",
            "16:00 to 16:30"
        ]
    },
    "Melissa": {
        "busy": [
            "09:30 to 10:00",
            "14:30 to 15:00"
        ]
    },
    "Frank": {
        "busy": [
            "10:00 to 10:30",
            "11:00 to 11:30",
            "12:30 to 13:00",
            "13:30 to 14:30",
            "15:00 to 16:00",
            "16:30 to 17:00"
        ],
        "constraints": [
            "not after 09:30"
        ]
    }
}

# Find a meeting time
start, end = find_meeting_time(participants_schedules, duration_minutes=30)
if start and end:
    print(f"Monday {{{start}:{end}}}")
else:
    print("No suitable time found.")