from datetime import datetime, timedelta

# Helper functions to convert time strings to minutes since midnight and vice versa
def time_to_minutes(time_str):
    t = datetime.strptime(time_str, "%H:%M")
    return t.hour * 60 + t.minute

def minutes_to_time(minutes):
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

# Working day parameters
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 60  # in minutes

# Busy intervals for each person on Monday (as minutes since midnight)
# Kayla's busy times: 10:00 to 10:30, 14:30 to 16:00
kayla_busy = [
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("14:30"), time_to_minutes("16:00"))
]

# Rebecca's busy times: 9:00 to 13:00, 13:30 to 15:00, 15:30 to 16:00
rebecca_busy = [
    (time_to_minutes("09:00"), time_to_minutes("13:00")),
    (time_to_minutes("13:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:00"))
]

def invert_intervals(busy, start, end):
    """Given busy intervals, return free intervals within [start, end]."""
    free = []
    current = start
    for b_start, b_end in sorted(busy):
        if b_start > current:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < end:
        free.append((current, end))
    return free

# Get free intervals for Kayla and Rebecca
kayla_free = invert_intervals(kayla_busy, work_start, work_end)
rebecca_free = invert_intervals(rebecca_busy, work_start, work_end)

def intersect_intervals(intervals1, intervals2):
    """Compute intersection of two lists of intervals."""
    i, j = 0, 0
    intersection = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Find overlap
        start_overlap = max(start1, start2)
        end_overlap = min(end1, end2)
        if start_overlap < end_overlap:
            intersection.append((start_overlap, end_overlap))
        # Move to next interval in the list that ends earlier
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersection

# Calculate common free intervals
common_free = intersect_intervals(kayla_free, rebecca_free)

# Find a slot with at least the meeting duration
meeting_slot = None
for start, end in common_free:
    if end - start >= meeting_duration:
        meeting_slot = (start, start + meeting_duration)
        break

if meeting_slot:
    meeting_start = minutes_to_time(meeting_slot[0])
    meeting_end = minutes_to_time(meeting_slot[1])
    print("Monday {" + meeting_start + ":" + meeting_end + "}")
else:
    print("No available time slot found.")