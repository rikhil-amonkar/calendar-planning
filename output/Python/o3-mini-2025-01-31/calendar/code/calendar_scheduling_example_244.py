from datetime import datetime, timedelta

def time_to_minutes(t_str):
    """Convert HH:MM string to minutes since midnight."""
    h, m = map(int, t_str.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes since midnight to HH:MM string."""
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def compute_free_intervals(busy_intervals, work_start, work_end):
    """
    Given a sorted list of busy intervals [(start, end), ...] in minutes,
    return a list of free intervals within [work_start, work_end].
    """
    free = []
    current = work_start
    for start, end in busy_intervals:
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    """
    Intersect two lists of intervals. Each interval is a tuple (start, end) in minutes.
    Both lists are assumed to be sorted by start time.
    Returns a sorted list of overlapping intervals.
    """
    i, j = 0, 0
    intersection = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Find overlap between intervals, if any.
        start_overlap = max(start1, start2)
        end_overlap = min(end1, end2)
        if start_overlap < end_overlap:
            intersection.append((start_overlap, end_overlap))
        # Move to the next interval in the list which ends first.
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersection

def find_common_free_intervals(free_intervals_dict):
    """
    Given a dictionary of participant:free_interval_list, compute the common free intervals.
    """
    participants = list(free_intervals_dict.keys())
    if not participants:
        return []
        
    common = free_intervals_dict[participants[0]]
    for participant in participants[1:]:
        common = intersect_intervals(common, free_intervals_dict[participant])
        if not common:
            break
    return common

def schedule_meeting(common_intervals, duration):
    """
    Given a list of intervals (in minutes) and meeting duration in minutes,
    return the first interval (start, end) that fits the meeting.
    """
    for start, end in common_intervals:
        if end - start >= duration:
            return start, start + duration
    return None

# Define work hours in minutes (9:00 to 17:00)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")

# Meeting duration: 30 minutes
meeting_duration = 30

# Busy schedules for each participant on Monday (in HH:MM format)
schedules = {
    "Walter": [],  # No busy intervals
    "Cynthia": [("09:00", "09:30"), ("10:00", "10:30"), ("13:30", "14:30"), ("15:00", "16:00")],
    "Ann": [("10:00", "11:00"), ("13:00", "13:30"), ("14:00", "15:00"), ("16:00", "16:30")],
    "Catherine": [("09:00", "11:30"), ("12:30", "13:30"), ("14:30", "17:00")],
    "Kyle": [("09:00", "09:30"), ("10:00", "11:30"), ("12:00", "12:30"), ("13:00", "14:30"), ("15:00", "16:00")]
}

# Convert busy intervals to minutes and sort them for each participant
busy_intervals_minutes = {}
for person, intervals in schedules.items():
    busy = []
    for start_str, end_str in intervals:
        start = time_to_minutes(start_str)
        end = time_to_minutes(end_str)
        busy.append((start, end))
    busy.sort()
    busy_intervals_minutes[person] = busy

# Compute free intervals for each participant within work hours
free_intervals = {}
for person, busy in busy_intervals_minutes.items():
    free_intervals[person] = compute_free_intervals(busy, work_start, work_end)

# Find common free intervals across all participants
common_free = find_common_free_intervals(free_intervals)

# Select a meeting time from the common free intervals that fits the duration
meeting_slot = schedule_meeting(common_free, meeting_duration)

day_of_week = "Monday"

if meeting_slot:
    meeting_start, meeting_end = meeting_slot
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    # Output format: HH:MM:HH:MM and the day of the week
    print(f"{start_str}:{end_str} {day_of_week}")
else:
    print("No available time slot found.")