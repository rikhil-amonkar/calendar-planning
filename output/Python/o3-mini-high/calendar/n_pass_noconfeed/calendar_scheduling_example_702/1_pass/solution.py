from datetime import datetime, timedelta

# Helper functions to convert between "HH:MM" strings and minutes
def to_minutes(time_str):
    """Convert HH:MM string to minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def to_time_str(minutes):
    """Convert minutes since midnight to HH:MM string."""
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    """
    Given a list of busy intervals (each a tuple of start and end times in minutes)
    and the work hours (work_start, work_end), return a list of free intervals.
    """
    free = []
    current = work_start
    for bstart, bend in sorted(busy_intervals):
        if current < bstart:
            free.append((current, bstart))
        current = max(current, bend)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    """
    Given two lists of intervals (each a tuple (start, end) in minutes), 
    return their intersections.
    """
    i, j = 0, 0
    intersections = []
    while i < len(intervals1) and j < len(intervals2):
        start = max(intervals1[i][0], intervals2[j][0])
        end = min(intervals1[i][1], intervals2[j][1])
        if start + meeting_duration <= end:
            intersections.append((start, end))
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return intersections

# Define work hours (in minutes) and meeting duration (in minutes)
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
meeting_duration = 30

# Define busy schedules (times in HH:MM format) for each participant on each day.
# Each value is a list of (start, end) tuples.
schedules = {
    "Monday": {
        "Robert": [("11:00", "11:30"), ("14:00", "14:30"), ("15:30", "16:00")],
        "Ralph":  [("10:00", "13:30"), ("14:00", "14:30"), ("15:00", "17:00")]
    },
    "Tuesday": {
        "Robert": [("10:30", "11:00"), ("15:00", "15:30")],
        "Ralph":  [("9:00", "9:30"), ("10:00", "10:30"), ("11:00", "11:30"),
                   ("12:00", "13:00"), ("14:00", "15:30"), ("16:00", "17:00")]
    },
    "Wednesday": {
        "Robert": [("10:00", "11:00"), ("11:30", "12:00"), ("12:30", "13:00"),
                   ("13:30", "14:00"), ("15:00", "15:30"), ("16:00", "16:30")],
        "Ralph":  [("10:30", "11:00"), ("11:30", "12:00"), ("13:00", "14:30"), ("16:30", "17:00")]
    }
}

# Preferred day order (avoid Monday if possible)
preferred_days = ["Tuesday", "Wednesday", "Monday"]

meeting_found = False

for day in preferred_days:
    # Convert busy intervals to minutes for each participant on the given day.
    robert_busy = [(to_minutes(start), to_minutes(end)) for start, end in schedules[day]["Robert"]]
    ralph_busy = [(to_minutes(start), to_minutes(end)) for start, end in schedules[day]["Ralph"]]
    
    # Get free intervals during work hours
    robert_free = get_free_intervals(robert_busy, work_start, work_end)
    ralph_free  = get_free_intervals(ralph_busy, work_start, work_end)
    
    # Get common free intervals between Robert and Ralph
    common_free = intersect_intervals(robert_free, ralph_free)
    
    # Look for an interval long enough for the meeting
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            meeting_found = True
            chosen_day = day
            break
    if meeting_found:
        break

if meeting_found:
    # Format the meeting time as HH:MM:HH:MM and output the day as well.
    meeting_time_str = f"{to_time_str(meeting_start)}:{to_time_str(meeting_end)}"
    print(f"{chosen_day} {meeting_time_str}")
else:
    print("No available meeting slot found.")