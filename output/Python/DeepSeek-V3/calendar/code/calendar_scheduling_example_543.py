def find_meeting_time(participants_schedules, work_hours_start, work_hours_end, duration_minutes, day):
    """
    Finds a meeting time that fits all participants' schedules.
    
    Args:
        participants_schedules: List of lists of busy time ranges for each participant.
        work_hours_start: Start of work hours in minutes from midnight (e.g., 9:00 AM is 540).
        work_hours_end: End of work hours in minutes from midnight (e.g., 5:00 PM is 1020).
        duration_minutes: Duration of the meeting in minutes.
        day: Day of the week (e.g., "Monday").
    
    Returns:
        A tuple of (start_time_str, end_time_str, day) if a slot is found, else None.
    """
    # Convert all busy times to minutes and merge overlapping or adjacent ranges
    def parse_time(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    def to_time_str(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    # Collect all busy time ranges from all participants
    all_busy = []
    for schedule in participants_schedules:
        for busy_range in schedule:
            start, end = map(parse_time, busy_range.split(' to '))
            all_busy.append((start, end))
    
    # Sort all busy ranges by start time
    all_busy.sort()
    
    # Merge overlapping or adjacent busy ranges
    merged_busy = []
    for start, end in all_busy:
        if not merged_busy:
            merged_busy.append((start, end))
        else:
            last_start, last_end = merged_busy[-1]
            if start <= last_end:
                # Overlapping or adjacent, merge them
                new_start = min(last_start, start)
                new_end = max(last_end, end)
                merged_busy[-1] = (new_start, new_end)
            else:
                merged_busy.append((start, end))
    
    # Check the available slots between work hours and busy times
    available_slots = []
    prev_end = work_hours_start
    
    for start, end in merged_busy:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    if prev_end < work_hours_end:
        available_slots.append((prev_end, work_hours_end))
    
    # Find the first available slot that can fit the meeting
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= duration_minutes:
            meeting_start = slot_start
            meeting_end = meeting_start + duration_minutes
            return (to_time_str(meeting_start), to_time_str(meeting_end), day)
    
    return None

# Define the participants' schedules
james_schedule = [
    "11:30 to 12:00",
    "14:30 to 15:00"
]

john_schedule = [
    "09:30 to 11:00",
    "11:30 to 12:00",
    "12:30 to 13:30",
    "14:30 to 16:30"
]

# Combine all participants' schedules
participants_schedules = [james_schedule, john_schedule]

# Define work hours and meeting duration
work_hours_start = 9 * 60  # 9:00 AM
work_hours_end = 17 * 60    # 5:00 PM
duration_minutes = 60
day = "Monday"

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, work_hours_start, work_hours_end, duration_minutes, day)

if meeting_time:
    start_time, end_time, day = meeting_time
    print(f"{start_time}:{end_time}:{day}")
else:
    print("No suitable meeting time found.")