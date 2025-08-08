def time_to_minutes(t):
    """Convert a time string 'HH:MM' to minutes since midnight."""
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes since midnight to a time string 'HH:MM'."""
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(working_start, working_end, blocked_intervals):
    """
    Given working hours [working_start, working_end] as strings and a list of 
    blocked intervals (each as a tuple of (start, end) in 'HH:MM' format),
    return a list of free intervals in minutes (start, end).
    """
    ws = time_to_minutes(working_start)
    we = time_to_minutes(working_end)
    
    # Convert and sort the blocked intervals by start time.
    blocks = []
    for b in blocked_intervals:
        start, end = b
        blocks.append((time_to_minutes(start), time_to_minutes(end)))
    blocks.sort()
    
    free = []
    current = ws
    for b_start, b_end in blocks:
        if b_start > current:
            free.append((current, min(b_start, we)))
        current = max(current, b_end)
        if current >= we:
            break
    if current < we:
        free.append((current, we))
    return free

def intersect_two(intervals1, intervals2):
    """
    Given two lists of intervals (each interval as a tuple (start, end) in minutes),
    return the list of intersections.
    """
    result = []
    for s1, e1 in intervals1:
        for s2, e2 in intervals2:
            start = max(s1, s2)
            end = min(e1, e2)
            if start < end:
                result.append((start, end))
    return result

def intersect_all(list_of_intervals):
    """Intersect a list of interval lists."""
    if not list_of_intervals:
        return []
    common = list_of_intervals[0]
    for intervals in list_of_intervals[1:]:
        common = intersect_two(common, intervals)
    return common

# Meeting parameters
meeting_duration = 30  # in minutes
meeting_day = "Monday"

# Participant blocked times (in 'HH:MM' format)
jeffrey_blocks = [("09:30", "10:00"), ("10:30", "11:00")]
virginia_blocks = [("09:00", "09:30"), ("10:00", "10:30"),
                   ("14:30", "15:00"), ("16:00", "16:30")]
melissa_blocks = [("09:00", "11:30"), ("12:00", "12:30"),
                  ("13:00", "15:00"), ("16:00", "17:00")]

# Working hours:
# Jeffrey and Virginia: 09:00 to 17:00
# Melissa prefers not to meet after 14:00, so we treat her working window as 09:00 to 14:00.
jeffrey_free = get_free_intervals("09:00", "17:00", jeffrey_blocks)
virginia_free = get_free_intervals("09:00", "17:00", virginia_blocks)
melissa_free = get_free_intervals("09:00", "14:00", melissa_blocks)

# Find the common free intervals for all participants
common_free = intersect_all([jeffrey_free, virginia_free, melissa_free])

# Choose the earliest interval that can accommodate the meeting
meeting_slot = None
for start, end in common_free:
    if end - start >= meeting_duration:
        meeting_slot = (start, start + meeting_duration)
        break

if meeting_slot:
    start_str = minutes_to_time(meeting_slot[0])
    end_str = minutes_to_time(meeting_slot[1])
    # Output in the format: day {HH:MM:HH:MM}
    print(f"{meeting_day} {{{start_str}:{end_str}}}")
else:
    print("No available time slot found.")