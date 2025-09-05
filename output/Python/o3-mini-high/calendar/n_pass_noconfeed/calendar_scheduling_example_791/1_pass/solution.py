def time_to_minutes(t):
    """Convert HH:MM string to minutes since midnight."""
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes since midnight to HH:MM string."""
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    """
    Given a list of busy intervals (each as (start, end) in minutes)
    and a work period [work_start, work_end], return a list of free intervals.
    """
    # First, sort the busy intervals
    busy_intervals = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current = work_start
    for bstart, bend in busy_intervals:
        # If the busy interval starts after our current free start
        if bstart > current:
            free.append((current, min(bstart, work_end)))
        current = max(current, bend)
        if current >= work_end:
            break
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(list1, list2):
    """Intersect two lists of intervals (each as (start, end))."""
    i, j = 0, 0
    intersection = []
    while i < len(list1) and j < len(list2):
        start = max(list1[i][0], list2[j][0])
        end = min(list1[i][1], list2[j][1])
        if start < end:
            intersection.append((start, end))
        if list1[i][1] < list2[j][1]:
            i += 1
        else:
            j += 1
    return intersection

# Define work hours in minutes (9:00 to 17:00)
WORK_START = time_to_minutes("09:00")  # 540
WORK_END = time_to_minutes("17:00")    # 1020
MEETING_DURATION = 30  # in minutes

# Define the schedules in HH:MM strings per day
schedules = {
    "Monday": {
        "Nicole": [("09:00", "09:30"), ("13:00", "13:30"), ("14:30", "15:30")],
        "Ruth": [("09:00", "17:00")]
    },
    "Tuesday": {
        "Nicole": [("09:00", "09:30"), ("11:30", "13:30"), ("14:30", "15:30")],
        "Ruth": [("09:00", "17:00")]
    },
    "Wednesday": {
        "Nicole": [("10:00", "11:00"), ("12:30", "15:00"), ("16:00", "17:00")],
        "Ruth": [("09:00", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"),
                 ("13:30", "15:30"), ("16:00", "16:30")]
        # Also note: Ruth does not want to meet after 13:30 on Wednesday.
    }
}

# Convert all busy times to minutes
for day in schedules:
    for person in schedules[day]:
        schedules[day][person] = [(time_to_minutes(start), time_to_minutes(end)) 
                                    for start, end in schedules[day][person]]

proposed_day = None
proposed_start = None
proposed_end = None

# Try each day in order
for day in ["Monday", "Tuesday", "Wednesday"]:
    # On Wednesday, Ruth prefers not to meet after 13:30,
    # so we restrict the effective work_end to 13:30 (810 minutes).
    effective_work_end = WORK_END
    if day == "Wednesday":
        effective_work_end = time_to_minutes("13:30")  # 810 minutes

    # Compute free intervals for all participants on this day.
    free_times = []
    for person in schedules[day]:
        busy = schedules[day][person]
        free = get_free_intervals(busy, WORK_START, effective_work_end)
        free_times.append(free)
    
    # Compute intersection of free intervals among all participants.
    if not free_times:
        continue
    common_free = free_times[0]
    for person_free in free_times[1:]:
        common_free = intersect_intervals(common_free, person_free)
    
    # Check if any common free interval can accommodate the meeting.
    for start, end in common_free:
        if end - start >= MEETING_DURATION:
            meeting_start = start
            meeting_end = meeting_start + MEETING_DURATION
            # For Wednesday, ensure the meeting ends by or at 13:30.
            if day == "Wednesday" and meeting_end > time_to_minutes("13:30"):
                continue
            proposed_day = day
            proposed_start = meeting_start
            proposed_end = meeting_end
            break
    if proposed_day:
        break

if proposed_day:
    # Format the meeting time as HH:MM:HH:MM and include the day.
    time_range = f"{minutes_to_time(proposed_start)}:{minutes_to_time(proposed_end)}"
    print(f"Proposed meeting time: {time_range} on {proposed_day}")
else:
    print("No available meeting time found.")