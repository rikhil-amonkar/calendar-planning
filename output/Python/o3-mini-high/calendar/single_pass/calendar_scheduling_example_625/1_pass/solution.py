def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define work hours (in minutes)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 30  # in minutes

# Harold's blocked time intervals for each day (Monday and Tuesday)
# Format: (start_time, end_time)
blocked = {
    "Monday": [("09:00", "10:00"), ("10:30", "17:00")],
    "Tuesday": [("09:00", "09:30"), ("10:30", "11:30"), 
                ("12:30", "13:30"), ("14:30", "15:30"), ("16:00", "17:00")]
}

# Harold's scheduling preferences:
# - Avoid Monday if possible.
# - On Tuesday, avoid meetings that start before 14:30.
preferred_day = "Tuesday"
tuesday_earliest_meeting = time_to_minutes("14:30")

def compute_free_intervals(day, blocks):
    """Compute free time intervals between work hours given blocked intervals."""
    free_intervals = []
    # Sort blocked intervals by their start time.
    sorted_blocks = sorted(blocks, key=lambda interval: time_to_minutes(interval[0]))
    current_time = work_start
    
    for start, end in sorted_blocks:
        block_start = time_to_minutes(start)
        block_end = time_to_minutes(end)
        if current_time < block_start:
            free_intervals.append((current_time, block_start))
        current_time = max(current_time, block_end)
    if current_time < work_end:
        free_intervals.append((current_time, work_end))
    return free_intervals

# Compute free intervals for Tuesday
free_intervals = compute_free_intervals(preferred_day, blocked[preferred_day])
meeting_slot = None

# Check each free interval and find one that fits the meeting duration
# while respecting the Tuesday preference (meeting start must be >= 14:30).
for interval_start, interval_end in free_intervals:
    # Adjust the start time to satisfy the Tuesday meeting preference.
    possible_start = max(interval_start, tuesday_earliest_meeting)
    if interval_end - possible_start >= meeting_duration:
        meeting_slot = (possible_start, possible_start + meeting_duration)
        break

if meeting_slot:
    start_str = minutes_to_time(meeting_slot[0])
    end_str = minutes_to_time(meeting_slot[1])
    # Output format: Day HH:MM:HH:MM  (e.g., Tuesday 15:30:16:00)
    print(f"{preferred_day} {start_str}:{end_str}")
else:
    print("No available meeting slot found that meets all constraints.")