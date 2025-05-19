from datetime import datetime, timedelta

# Helper function to convert time string (HH:MM) to minutes since midnight
def time_to_minutes(t_str):
    h, m = map(int, t_str.split(":"))
    return h * 60 + m

# Helper function to convert minutes since midnight to time string (HH:MM)
def minutes_to_time(m):
    return f"{m//60:02d}:{m%60:02d}"

# Meeting duration in minutes and work day boundaries (in minutes)
meeting_duration = 30
day_start = time_to_minutes("09:00")
day_end = time_to_minutes("17:00")
avoid_after = time_to_minutes("15:00")  # Bobby wants to avoid meetings after 15:00

# Busy schedules for each participant on Monday: list of (start, end) time in minutes
schedules = {
    "Lisa": [
        (time_to_minutes("09:00"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("11:30")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ],
    "Bobby": [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("15:00"), time_to_minutes("15:30"))
    ],
    "Randy": [
        (time_to_minutes("09:30"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:30")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ]
}

# This function returns the free intervals for a person given the busy intervals,
# constrained to be within the work day hours.
def get_free_intervals(busy_intervals):
    free_intervals = []
    # Start with the beginning of the day
    current_start = day_start
    for start, end in sorted(busy_intervals):
        if current_start < start:
            free_intervals.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < day_end:
        free_intervals.append((current_start, day_end))
    return free_intervals

# Get free intervals for all participants
free_intervals_all = {}
for person, busy in schedules.items():
    free_intervals_all[person] = get_free_intervals(busy)

# Function to intersect two sets of intervals
def intersect_intervals(intervals1, intervals2):
    i, j = 0, 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # find overlap between intervals
        overlap_start = max(start1, start2)
        overlap_end = min(end1, end2)
        if overlap_end - overlap_start >= meeting_duration:
            result.append((overlap_start, overlap_end))
        # Move next based on which interval ends earlier
        if end1 < end2:
            i += 1
        else:
            j += 1
    return result

# Calculate the common free intervals for all participants
common_free = free_intervals_all["Lisa"]
for person in ["Bobby", "Randy"]:
    common_free = intersect_intervals(common_free, free_intervals_all[person])

# Also, Bobby prefers to avoid meetings after 15:00,
# so we need to restrict the available intervals to end by 15:00.
adjusted_free = []
for start, end in common_free:
    # If the interval starts after or at 15:00, skip it
    if start >= avoid_after:
        continue
    # Adjust end to the minimum of original end and Bobby's avoid_after time
    adjusted_end = min(end, avoid_after)
    if adjusted_end - start >= meeting_duration:
        adjusted_free.append((start, adjusted_end))

# Select the earliest possible interval that can accommodate the meeting
meeting_start = None
for start, end in adjusted_free:
    if end - start >= meeting_duration:
        meeting_start = start
        break

if meeting_start is None:
    print("No available meeting slot found within the constraints.")
else:
    meeting_end = meeting_start + meeting_duration
    # Format the meeting time in HH:MM:HH:MM
    meeting_time_str = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
    # Print the proposed meeting time and day of the week
    day_of_week = "Monday"
    print(meeting_time_str, day_of_week)