def time_to_minutes(t):
    """Convert time string 'HH:MM' to minutes since midnight."""
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes since midnight to time string 'HH:MM'."""
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def subtract_intervals(whole, blocks):
    """
    Given a whole interval (start, end) and a list of block intervals,
    return a list of intervals representing the free time.
    whole: tuple of (start, end) in minutes.
    blocks: list of tuples (start, end) in minutes.
    """
    free = []
    start_whole, end_whole = whole
    current_start = start_whole
    for b_start, b_end in sorted(blocks):
        if b_start > current_start:
            free.append((current_start, min(b_start, end_whole)))
        current_start = max(current_start, b_end)
        if current_start >= end_whole:
            break
    if current_start < end_whole:
        free.append((current_start, end_whole))
    return free

def intersect_intervals(intv1, intv2):
    """
    Given two lists of intervals, return their intersection as a list of intervals.
    Each interval is a tuple (start, end) in minutes.
    """
    intersection = []
    i, j = 0, 0
    while i < len(intv1) and j < len(intv2):
        start1, end1 = intv1[i]
        start2, end2 = intv2[j]
        # Find intersection between these two intervals
        start = max(start1, start2)
        end = min(end1, end2)
        if start < end:
            intersection.append((start, end))
        # Move to next interval in the list that ends first
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersection

# Meeting details
MEETING_DURATION = 30  # minutes
DAY = "Monday"

# Work hours for everyone (in minutes)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
work_interval = (work_start, work_end)

# Existing meetings in minutes
# Christine's meetings on Monday
christine_meetings = [
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("15:00"), time_to_minutes("15:30"))
]

# Helen's meetings on Monday (blocks)
helen_meetings = [
    (time_to_minutes("09:30"), time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:30"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Additional constraint: Helen cannot meet on Monday after 15:00.
# So, for Helen, adjust work interval end to 15:00.
helen_work_interval = (work_start, time_to_minutes("15:00"))

# Calculate free intervals for each participant
christine_free = subtract_intervals(work_interval, christine_meetings)
helen_free = subtract_intervals(helen_work_interval, helen_meetings)

# Find intersections of free intervals between Christine and Helen
common_free = intersect_intervals(christine_free, helen_free)

# Now search for a free slot that can accommodate the meeting duration.
proposed_slot = None
for start, end in common_free:
    if end - start >= MEETING_DURATION:
        proposed_slot = (start, start + MEETING_DURATION)
        break

if proposed_slot:
    start_time = minutes_to_time(proposed_slot[0])
    end_time   = minutes_to_time(proposed_slot[1])
    # Output format: HH:MM:HH:MM and day of week
    print(f"{start_time}:{end_time} {DAY}")
else:
    print("No available slot found.")