def find_meeting_time(participants_schedules, meeting_duration, work_hours, preferences=None):
    """
    Find a meeting time that fits all participants' schedules and constraints.
    
    Args:
        participants_schedules (dict): Dictionary with each participant's busy times.
        meeting_duration (int): Duration of the meeting in minutes.
        work_hours (tuple): Start and end of work hours in 'HH:MM' format.
        preferences (dict, optional): Any preferences like avoiding certain times.
    
    Returns:
        tuple: (day, start_time, end_time) if found, else (None, None, None).
    """
    day = "Monday"  # As per the task, the day is fixed
    
    # Convert work hours to minutes since midnight for easier calculation
    work_start = sum(x * int(t) for x, t in zip([60, 1], work_hours[0].split(':')))
    work_end = sum(x * int(t) for x, t in zip([60, 1], work_hours[1].split(':')))
    
    # Collect all busy intervals for all participants
    all_busy = []
    for person, schedules in participants_schedules.items():
        for interval in schedules:
            start = sum(x * int(t) for x, t in zip([60, 1], interval[0].split(':')))
            end = sum(x * int(t) for x, t in zip([60, 1], interval[1].split(':')))
            all_busy.append((start, end))
    
    # Sort all busy intervals by start time
    all_busy.sort()
    
    # Merge overlapping or adjacent busy intervals
    merged = []
    for start, end in all_busy:
        if not merged:
            merged.append((start, end))
        else:
            last_start, last_end = merged[-1]
            if start <= last_end:
                new_start = min(last_start, start)
                new_end = max(last_end, end)
                merged[-1] = (new_start, new_end)
            else:
                merged.append((start, end))
    
    # Find available slots between work hours and busy intervals
    available = []
    prev_end = work_start
    
    for start, end in merged:
        if start > prev_end:
            available.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    if prev_end < work_end:
        available.append((prev_end, work_end))
    
    # Check preferences (e.g., Bobby wants to avoid after 15:00)
    if preferences:
        avoid_after = preferences.get('avoid_after', None)
        if avoid_after:
            avoid_minutes = sum(x * int(t) for x, t in zip([60, 1], avoid_after.split(':')))
            available = [slot for slot in available if slot[1] <= avoid_minutes]
    
    # Find the first available slot that fits the meeting duration
    for start, end in available:
        if end - start >= meeting_duration:
            # Convert back to HH:MM format
            start_hh = start // 60
            start_mm = start % 60
            end_time = start + meeting_duration
            end_hh = end_time // 60
            end_mm = end_time % 60
            return (
                day,
                f"{start_hh:02d}:{start_mm:02d}",
                f"{end_hh:02d}:{end_mm:02d}"
            )
    
    return (None, None, None)

# Define the participants' schedules
participants_schedules = {
    "Lisa": [
        ("9:00", "10:00"),
        ("10:30", "11:30"),
        ("12:30", "13:00"),
        ("16:00", "16:30"),
    ],
    "Bobby": [
        ("9:00", "9:30"),
        ("10:00", "10:30"),
        ("11:30", "12:00"),
        ("15:00", "15:30"),
    ],
    "Randy": [
        ("9:30", "10:00"),
        ("10:30", "11:00"),
        ("11:30", "12:30"),
        ("13:00", "13:30"),
        ("14:30", "15:30"),
        ("16:00", "16:30"),
    ],
}

# Define meeting duration (30 minutes) and work hours (9:00 to 17:00)
meeting_duration = 30
work_hours = ("9:00", "17:00")

# Define Bobby's preference to avoid meetings after 15:00
preferences = {"avoid_after": "15:00"}

# Find the meeting time
day, start_time, end_time = find_meeting_time(
    participants_schedules,
    meeting_duration,
    work_hours,
    preferences
)

# Output the result
print(f"{day}: {start_time}:{end_time}")