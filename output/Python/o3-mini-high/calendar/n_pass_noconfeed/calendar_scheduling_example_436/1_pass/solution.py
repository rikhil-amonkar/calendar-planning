def time_to_minutes(time_str):
    """Converts a 'HH:MM' string to minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Converts minutes since midnight to a 'HH:MM' string."""
    return f"{minutes//60:02d}:{minutes%60:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    """Given a sorted list of busy intervals (in minutes) within work_start and work_end,
    return a list of free intervals."""
    free = []
    current = work_start
    for start, end in busy_intervals:
        if current < start:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    """Return the intersection of two lists of intervals."""
    i, j = 0, 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        start = max(intervals1[i][0], intervals2[j][0])
        end = min(intervals1[i][1], intervals2[j][1])
        if start < end:  # There is an overlap.
            result.append((start, end))
        # Move to the next interval in the list which ends earlier.
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return result

# Define working hours for Monday
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 30  # minutes

# Define each participant's busy intervals on Monday in HH:MM format.
schedules = {
    "Patrick": [("13:30", "14:00"), ("14:30", "15:00")],
    "Shirley": [("09:00", "09:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("14:30", "15:00"), ("16:00", "17:00")],
    "Jeffrey": [("09:00", "09:30"), ("10:30", "11:00"), ("11:30", "12:00"), ("13:00", "13:30"), ("16:00", "17:00")],
    "Gloria": [("11:30", "12:00"), ("15:00", "15:30")],
    "Nathan": [("09:00", "09:30"), ("10:30", "12:00"), ("14:00", "17:00")],
    "Angela": [("09:00", "09:30"), ("10:00", "11:00"), ("12:30", "15:00"), ("15:30", "16:30")],
    "David": [("09:00", "09:30"), ("10:00", "10:30"), ("11:00", "14:00"), ("14:30", "16:30")]
}

# Convert busy intervals to minutes and sort them (just in case)
busy_intervals_all = {}
for person, intervals in schedules.items():
    converted = [(time_to_minutes(start), time_to_minutes(end)) for start, end in intervals]
    converted.sort(key=lambda x: x[0])
    busy_intervals_all[person] = converted

# Compute free intervals for every participant
free_intervals_all = {}
for person, busy in busy_intervals_all.items():
    free_intervals = get_free_intervals(busy, work_start, work_end)
    free_intervals_all[person] = free_intervals

# Compute common free intervals by intersecting free intervals of every participant.
# Start with the free intervals of one person, then intersect with others.
participants = list(free_intervals_all.keys())
common_free = free_intervals_all[participants[0]]
for person in participants[1:]:
    common_free = intersect_intervals(common_free, free_intervals_all[person])

# Find the earliest common free interval that can accommodate the meeting_duration.
proposed_meeting = None
for start, end in common_free:
    if end - start >= meeting_duration:
        proposed_meeting = (start, start + meeting_duration)
        break

if proposed_meeting:
    start_str = minutes_to_time(proposed_meeting[0])
    end_str = minutes_to_time(proposed_meeting[1])
    # Output in the format HH:MM:HH:MM and the day of the week.
    print(f"Monday {start_str}:{end_str}")
else:
    print("No suitable time slot found.")