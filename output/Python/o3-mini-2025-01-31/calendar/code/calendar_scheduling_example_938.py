from datetime import timedelta, datetime

# Helper functions
def time_to_minutes(t):
    # t in "HH:MM" format
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    minute = m % 60
    return f"{h:02d}:{minute:02d}"

def merge_intervals(intervals):
    """Merge overlapping intervals; each interval is a tuple (start, end) in minutes."""
    if not intervals:
        return []
    intervals.sort(key=lambda x: x[0])
    merged = [intervals[0]]
    for current in intervals[1:]:
        prev = merged[-1]
        if current[0] <= prev[1]:
            merged[-1] = (prev[0], max(prev[1], current[1]))
        else:
            merged.append(current)
    return merged

def invert_intervals(busy, start, end):
    """Given busy intervals (merged) in [start, end], return free intervals."""
    free = []
    current = start
    for b_start, b_end in busy:
        if b_start > current:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < end:
        free.append((current, end))
    return free

def intersect_intervals(intervals1, intervals2):
    """Return intersections of two lists of intervals."""
    i, j = 0, 0
    intersections = []
    while i < len(intervals1) and j < len(intervals2):
        start = max(intervals1[i][0], intervals2[j][0])
        end = min(intervals1[i][1], intervals2[j][1])
        if start < end:
            intersections.append((start, end))
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return intersections

# Define business hours and meeting duration in minutes
business_start = time_to_minutes("09:00")
business_end = time_to_minutes("17:00")
meeting_duration = 30

# Busy schedules for each participant defined by day.
# Each busy interval is defined as (start, end) in "HH:MM" string format.
schedules = {
    "Eugene": {
        "Monday": [("11:00", "12:00"), ("13:30", "14:00"), ("14:30", "15:00"), ("16:00", "16:30")],
        "Tuesday": [],  # No busy intervals mentioned for Tuesday for Eugene.
        "Wednesday": [("09:00", "09:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("13:30", "15:00")],
        "Thursday": [("09:30", "10:00"), ("11:00", "12:30")],
        "Friday": [("10:30", "11:00"), ("12:00", "12:30"), ("13:00", "13:30")]
    },
    "Eric": {
        "Monday": [("09:00", "17:00")],
        "Tuesday": [("09:00", "17:00")],
        "Wednesday": [("09:00", "11:30"), ("12:00", "14:00"), ("14:30", "16:30")],
        "Thursday": [("09:00", "17:00")],
        "Friday": [("09:00", "11:00"), ("11:30", "17:00")]
    }
}

# Days of week in the acceptable order.
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

# Eric's preference is to avoid Wednesday if possible.
# So we'll check non-Wednesday days first.
preferred_days = [d for d in days if d != "Wednesday"] + ["Wednesday"]

# Candidate meeting slots: list of (day, start, end)
candidates = []

for day in preferred_days:
    # Get Eugene's busy intervals and convert to minutes
    e_segments = []
    for start_str, end_str in schedules["Eugene"].get(day, []):
        start = time_to_minutes(start_str)
        end = time_to_minutes(end_str)
        e_segments.append((start, end))
    e_busy = merge_intervals(e_segments)
    e_free = invert_intervals(e_busy, business_start, business_end)
    
    # Get Eric's busy intervals and convert to minutes
    er_segments = []
    for start_str, end_str in schedules["Eric"].get(day, []):
        start = time_to_minutes(start_str)
        end = time_to_minutes(end_str)
        er_segments.append((start, end))
    er_busy = merge_intervals(er_segments)
    er_free = invert_intervals(er_busy, business_start, business_end)
    
    # Find common free intervals
    common_free = intersect_intervals(e_free, er_free)
    
    # Check if any common free interval can accommodate the meeting
    for free_start, free_end in common_free:
        if free_end - free_start >= meeting_duration:
            # Use the first available slot in that free interval
            meeting_start = free_start
            meeting_end = meeting_start + meeting_duration
            candidates.append((day, meeting_start, meeting_end))
            break  # Stop after finding the first valid slot for this day

# Select the first candidate in the ordered preferred_days list.
if candidates:
    day, start, end = candidates[0]
    meeting_time = f"{minutes_to_time(start)}:{minutes_to_time(end)}"
    print(f"{day}, {meeting_time}")
else:
    print("No suitable meeting slot found.")