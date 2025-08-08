def time_to_minutes(time_str):
    """Converts a time in HH:MM format to minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Converts minutes since midnight to HH:MM format."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def free_intervals(busy_list, work_start, work_end):
    """
    Given a sorted list of busy intervals (each as a tuple of (start, end) in minutes)
    and the overall working period, returns a list of free intervals.
    """
    free = []
    current = work_start
    for start, end in busy_list:
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    """Intersects two lists of intervals and returns the overlapping segments."""
    i, j = 0, 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        start = max(intervals1[i][0], intervals2[j][0])
        end = min(intervals1[i][1], intervals2[j][1])
        if start < end:
            result.append((start, end))
        # Move to the next interval in the list that ends first.
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return result

# Define working hours for Monday
work_start = time_to_minutes("09:00")
work_end   = time_to_minutes("17:00")

# Busy schedules for participants on Monday
busy_schedules = {
    "Gregory":   [("09:00", "09:30"), ("11:30", "12:00")],
    "Jonathan":  [("09:00", "09:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("15:00", "16:00"), ("16:30", "17:00")],
    "Barbara":   [("10:00", "10:30"), ("13:30", "14:00")],
    "Jesse":     [("10:00", "11:00"), ("12:30", "14:30")],
    "Alan":      [("09:30", "11:00"), ("11:30", "12:30"), ("13:00", "15:30"), ("16:00", "17:00")],
    "Nicole":    [("09:00", "10:30"), ("11:30", "12:00"), ("12:30", "13:30"), ("14:00", "17:00")],
    "Catherine": [("09:00", "10:30"), ("12:00", "13:30"), ("15:00", "15:30"), ("16:00", "16:30")]
}

# Convert busy times to minutes for each participant
for person, intervals in busy_schedules.items():
    busy_schedules[person] = [(time_to_minutes(start), time_to_minutes(end)) for start, end in intervals]

# Compute free time intervals for each participant from the working hours.
free_times = {}
for person, busy_list in busy_schedules.items():
    # Ensure the busy intervals are sorted.
    busy_list_sorted = sorted(busy_list, key=lambda x: x[0])
    free_times[person] = free_intervals(busy_list_sorted, work_start, work_end)

# Compute the common free intervals by intersecting everyone's free intervals.
participants = list(free_times.keys())
common_free = free_times[participants[0]]
for person in participants[1:]:
    common_free = intersect_intervals(common_free, free_times[person])

# We need a meeting slot of 30 minutes.
meeting_duration = 30
meeting_slot = None
for start, end in common_free:
    if end - start >= meeting_duration:
        meeting_slot = (start, start + meeting_duration)
        break

if meeting_slot:
    meeting_time = f"{minutes_to_time(meeting_slot[0])}:{minutes_to_time(meeting_slot[1])}"
    day_of_week = "Monday"
    print(f"{meeting_time} on {day_of_week}")
else:
    print("No available time slot found")