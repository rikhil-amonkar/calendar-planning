def time_to_minutes(t):
    """Convert time string 'HH:MM' to minutes since midnight."""
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes since midnight to time string 'HH:MM'."""
    return f"{m // 60:02d}:{m % 60:02d}"

def get_free_intervals(busy, work_start, work_end):
    """
    Given a list of busy intervals (tuples of (start, end) in minutes), 
    return a list of free intervals within the work hours [work_start, work_end].
    """
    free = []
    current = work_start
    for b_start, b_end in sorted(busy):
        if current < b_start:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_two(intervals1, intervals2):
    """Return the intersection of two lists of intervals."""
    i, j = 0, 0
    intersection = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Find the overlap between intervals
        start_overlap = max(start1, start2)
        end_overlap = min(end1, end2)
        if start_overlap < end_overlap:
            intersection.append((start_overlap, end_overlap))
        # Move to the next interval in the list that ends first
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersection

def intersect_all(intervals_list):
    """Return the intersection among multiple lists of intervals."""
    if not intervals_list:
        return []
    current = intervals_list[0]
    for intervals in intervals_list[1:]:
        current = intersect_two(current, intervals)
    return current

# Define work hours (in minutes; 9:00 = 540, 17:00 = 1020)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 60  # in minutes

# Busy schedules for each participant for each day.
# Each time is represented as a tuple (start, end) in "HH:MM" format.
schedules = {
    "Monday": {
        "Carl": [("11:00", "11:30")],
        "Margaret": [("09:00", "10:30"), ("11:00", "17:00")]
    },
    "Tuesday": {
        "Carl": [("14:30", "15:00")],
        "Margaret": [("09:30", "12:00"), ("13:30", "14:00"), ("15:30", "17:00")]
    },
    "Wednesday": {
        "Carl": [("10:00", "11:30"), ("13:00", "13:30")],
        "Margaret": [("09:30", "12:00"), ("12:30", "13:00"), ("13:30", "14:30"), ("15:00", "17:00")]
    },
    "Thursday": {
        "Carl": [("13:30", "14:00"), ("16:00", "16:30")],
        "Margaret": [("10:00", "12:00"), ("12:30", "14:00"), ("14:30", "17:00")]
    }
}

# Carl prefers to avoid Thursday, so we try other days first.
ordered_days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

selected_day = None
selected_start = None

for day in ordered_days:
    # Get free intervals for each participant for the current day.
    free_intervals_all = []
    for person in schedules[day]:
        # Convert busy times to minutes
        busy_intervals = [(time_to_minutes(start), time_to_minutes(end)) for start, end in schedules[day][person]]
        free = get_free_intervals(busy_intervals, work_start, work_end)
        free_intervals_all.append(free)
    # Compute common free intervals among participants
    common_free = intersect_all(free_intervals_all)
    # Look for an interval that can fit the meeting duration.
    for start, end in common_free:
        if end - start >= meeting_duration:
            selected_day = day
            selected_start = start
            break
    if selected_day:
        # Stop at the first available day.
        break

# Choose the meeting time if available.
if selected_day is not None:
    meeting_start = selected_start
    meeting_end = meeting_start + meeting_duration
    # Format the result as "HH:MM:HH:MM" and include the day.
    time_range = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
    print(f"{selected_day} {time_range}")
else:
    print("No meeting slot available.")