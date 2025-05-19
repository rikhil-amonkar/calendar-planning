from datetime import datetime, timedelta

# Helper functions to convert time strings to minutes and vice versa
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

# Function to compute free intervals given busy intervals within a work period
def get_free_intervals(busy_intervals, work_start, work_end):
    free = []
    current = work_start
    # Ensure busy intervals are sorted
    busy_intervals.sort(key=lambda x: x[0])
    for interval in busy_intervals:
        start_busy, end_busy = interval
        if start_busy > current:
            free.append((current, start_busy))
        current = max(current, end_busy)
    if current < work_end:
        free.append((current, work_end))
    return free

# Function to intersect two lists of intervals
def intersect_intervals(list1, list2):
    i, j = 0, 0
    intersection = []
    while i < len(list1) and j < len(list2):
        a_start, a_end = list1[i]
        b_start, b_end = list2[j]
        # Find the overlap between the two intervals
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            intersection.append((start, end))
        # Move on from the interval that ends first
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return intersection

# Work day start and end times in minutes (9:00 to 17:00)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 30  # minutes

# Busy schedules for each participant on Monday (times in minutes)
busy_bradley = [
    (time_to_minutes("09:30"), time_to_minutes("10:00")),
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("13:30"), time_to_minutes("14:00")),
    (time_to_minutes("15:30"), time_to_minutes("16:00"))
]

busy_teresa = [
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("15:00"))
]

busy_elizabeth = [
    (time_to_minutes("09:00"), time_to_minutes("09:30")),
    (time_to_minutes("10:30"), time_to_minutes("11:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("17:00"))
]

busy_christian = [
    (time_to_minutes("09:00"), time_to_minutes("09:30")),
    (time_to_minutes("10:30"), time_to_minutes("17:00"))
]

# Compute free intervals for each participant
free_bradley = get_free_intervals(busy_bradley, work_start, work_end)
free_teresa = get_free_intervals(busy_teresa, work_start, work_end)
free_elizabeth = get_free_intervals(busy_elizabeth, work_start, work_end)
free_christian = get_free_intervals(busy_christian, work_start, work_end)

# Intersect all free intervals to get common free slots
common_free = intersect_intervals(free_bradley, free_teresa)
common_free = intersect_intervals(common_free, free_elizabeth)
common_free = intersect_intervals(common_free, free_christian)

# Find the first interval that can accommodate the meeting duration
meeting_start = None
for start, end in common_free:
    if end - start >= meeting_duration:
        meeting_start = start
        meeting_end = start + meeting_duration
        break

if meeting_start is not None:
    meeting_time = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
    day_of_week = "Monday"
    print(meeting_time)
    print(day_of_week)
else:
    print("No available time slot found.")