def time_to_minutes(time_str):
    """Converts a HH:MM time string to minutes past midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Converts minutes past midnight to a HH:MM formatted string."""
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def get_free_intervals(busy, window_start, window_end):
    """
    Given a list of busy intervals (tuples of start and end in minutes)
    within a window, returns a list of free intervals as tuples (start, end).
    """
    free = []
    current = window_start
    # Ensure busy intervals are sorted
    busy = sorted(busy, key=lambda x: x[0])
    for b_start, b_end in busy:
        if b_end <= current:
            continue
        if b_start > current:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < window_end:
        free.append((current, window_end))
    return free

def intersect_intervals(intervals1, intervals2):
    """
    Intersects two lists of intervals and returns the overlapping parts.
    """
    result = []
    i, j = 0, 0
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Find the overlap between the two intervals
        overlap_start = max(start1, start2)
        overlap_end = min(end1, end2)
        if overlap_start < overlap_end:
            result.append((overlap_start, overlap_end))
        # Move to the next interval in the list that ends earlier
        if end1 < end2:
            i += 1
        else:
            j += 1
    return result

def clip_interval(interval, window_start, window_end):
    """
    Clip an interval to lie within the boundaries of the window [window_start, window_end].
    Returns None if there is no overlap.
    """
    start, end = interval
    start = max(start, window_start)
    end = min(end, window_end)
    if start < end:
        return (start, end)
    return None

# Parameters for the meeting
meeting_duration = 30  # in minutes
meeting_day = "Monday"
# Full work day is 09:00 to 17:00, but Helen prefers not to meet after 13:30.
# So we limit the effective meeting window to 09:00 - 13:30.
window_start = time_to_minutes("09:00")
window_end = time_to_minutes("13:30")

# Define the busy times for each participant (only times that intersect our effective window)
# Times are given as HH:MM strings; we will clip them to [window_start, window_end] if necessary.

# Margaret's busy times on Monday:
margaret_busy_times = [("09:00", "10:00"),
                       ("10:30", "11:00"),
                       ("11:30", "12:00"),
                       ("13:00", "13:30"),
                       # ("15:00", "15:30") is outside the effective window so we ignore it
                      ]
margaret_busy = []
for start_str, end_str in margaret_busy_times:
    interval = (time_to_minutes(start_str), time_to_minutes(end_str))
    clipped = clip_interval(interval, window_start, window_end)
    if clipped:
        margaret_busy.append(clipped)

# Donna's busy times on Monday:
donna_busy_times = [("14:30", "15:00"), ("16:00", "16:30")]
donna_busy = []
for start_str, end_str in donna_busy_times:
    interval = (time_to_minutes(start_str), time_to_minutes(end_str))
    clipped = clip_interval(interval, window_start, window_end)
    if clipped:
        donna_busy.append(clipped)
# In this effective window, Donna is fully free.

# Helen's busy times on Monday:
helen_busy_times = [("09:00", "09:30"),
                    ("10:00", "11:30"),
                    ("13:00", "14:00"),
                    # The remaining busy times are outside the effective window.
                   ]
helen_busy = []
for start_str, end_str in helen_busy_times:
    interval = (time_to_minutes(start_str), time_to_minutes(end_str))
    clipped = clip_interval(interval, window_start, window_end)
    if clipped:
        helen_busy.append(clipped)

# Compute free intervals for each participant within our effective window
margaret_free = get_free_intervals(margaret_busy, window_start, window_end)
donna_free = get_free_intervals(donna_busy, window_start, window_end)
helen_free = get_free_intervals(helen_busy, window_start, window_end)

# Find the common free intervals among all participants by intersection
common_free = intersect_intervals(margaret_free, donna_free)
common_free = intersect_intervals(common_free, helen_free)

# Select the earliest interval that is long enough for the meeting
proposed_start = None
for start, end in common_free:
    if end - start >= meeting_duration:
        proposed_start = start
        break

if proposed_start is not None:
    proposed_end = proposed_start + meeting_duration
    # Format the meeting time as HH:MM:HH:MM (start:end)
    meeting_time = f"{minutes_to_time(proposed_start)}:{minutes_to_time(proposed_end)}"
    print(f"{meeting_day} {meeting_time}")
else:
    print("No available meeting time found.")