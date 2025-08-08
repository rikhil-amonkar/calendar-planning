def time_to_minutes(time_str):
    """Convert a HH:MM string to minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to a HH:MM string."""
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

WORK_START = time_to_minutes("09:00")
WORK_END = time_to_minutes("17:00")
MEETING_DURATION = 30  # duration in minutes

# Busy schedules in the format (start_time, end_time)
# Times are strings in HH:MM format.
schedule = {
    "Monday": {
        "Bobby": [("14:30", "15:00")],
        "Michael": [("09:00", "10:00"), ("10:30", "13:30"),
                    ("14:00", "15:00"), ("15:30", "17:00")]
    },
    "Tuesday": {
        "Bobby": [("09:00", "11:30"), ("12:00", "12:30"),
                  ("13:00", "15:00"), ("15:30", "17:00")],
        "Michael": [("09:00", "10:30"), ("11:00", "11:30"),
                    ("12:00", "14:00"), ("15:00", "16:00"),
                    ("16:30", "17:00")]
    }
}

def compute_free_intervals(busy_intervals):
    """
    Given a list of busy intervals (in minutes) for a day,
    compute free intervals within the working hours.
    """
    free_intervals = []
    current = WORK_START
    for start, end in busy_intervals:
        if start > current:
            free_intervals.append((current, start))
        if end > current:
            current = end
    if current < WORK_END:
        free_intervals.append((current, WORK_END))
    return free_intervals

def intersect_intervals(intervals1, intervals2):
    """Return the list of intersections between two lists of intervals."""
    intersections = []
    i, j = 0, 0
    while i < len(intervals1) and j < len(intervals2):
        a_start, a_end = intervals1[i]
        b_start, b_end = intervals2[j]
        # Find the overlapping interval, if it exists.
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            intersections.append((start, end))
        # Move to the next interval from the one which ends first.
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return intersections

# Check each day (Monday then Tuesday) for the earliest available meeting slot.
meeting_day = None
meeting_slot = None

for day in ["Monday", "Tuesday"]:
    # Convert busy time strings to minute intervals for each participant.
    bobby_busy = sorted(
        [(time_to_minutes(start), time_to_minutes(end)) for start, end in schedule[day]["Bobby"]],
        key=lambda x: x[0]
    )
    michael_busy = sorted(
        [(time_to_minutes(start), time_to_minutes(end)) for start, end in schedule[day]["Michael"]],
        key=lambda x: x[0]
    )
    
    # Compute free intervals within working hours for each.
    bobby_free = compute_free_intervals(bobby_busy)
    michael_free = compute_free_intervals(michael_busy)
    
    # Find common free intervals.
    common_free = intersect_intervals(bobby_free, michael_free)
    
    # Look for the first common free interval that can accommodate the meeting.
    for start, end in common_free:
        if (end - start) >= MEETING_DURATION:
            meeting_day = day
            meeting_slot = (start, start + MEETING_DURATION)
            break
    if meeting_slot:
        break

if meeting_slot and meeting_day:
    start_time = minutes_to_time(meeting_slot[0])
    end_time = minutes_to_time(meeting_slot[1])
    # Output in the format: Day {HH:MM:HH:MM}
    print(f"{meeting_day} {{{start_time}:{end_time}}}")
else:
    print("No available meeting time found.")