def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(work_start, work_end, blocked_intervals):
    # Assumes blocked_intervals are sorted and within [work_start, work_end]
    free_intervals = []
    current = work_start
    for b_start, b_end in sorted(blocked_intervals):
        if b_start > current:
            free_intervals.append((current, b_start))
        current = max(current, b_end)
    if current < work_end:
        free_intervals.append((current, work_end))
    return free_intervals

def intersect_intervals(list1, list2):
    i, j = 0, 0
    intersection = []
    while i < len(list1) and j < len(list2):
        start1, end1 = list1[i]
        start2, end2 = list2[j]
        # Calculate overlap between the two intervals
        start = max(start1, start2)
        end = min(end1, end2)
        if start < end:
            intersection.append((start, end))
        # Move to the next interval from the list which ends earlier
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersection

def find_meeting_slot(common_intervals, duration):
    for start, end in common_intervals:
        if end - start >= duration:
            return start, start + duration
    return None

# Effective working window is determined by work hours (09:00 to 17:00)
# and Billy's preference (avoid meetings after 15:00).
# So we use 09:00 to 15:00.
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("15:00")
meeting_duration = 30  # in minutes

# Blocked intervals in minutes for each participant (only those within 09:00-15:00)
# Raymond's blocked times: 09:00-09:30, 11:30-12:00, 13:00-13:30
raymond_blocked = [
    (time_to_minutes("09:00"), time_to_minutes("09:30")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
]

# Billy's blocked times: 10:00-10:30, 12:00-13:00
billy_blocked = [
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("12:00"), time_to_minutes("13:00")),
]

# Donald's blocked times: 09:00-09:30, 10:00-11:00, 12:00-13:00, 14:00-14:30
donald_blocked = [
    (time_to_minutes("09:00"), time_to_minutes("09:30")),
    (time_to_minutes("10:00"), time_to_minutes("11:00")),
    (time_to_minutes("12:00"), time_to_minutes("13:00")),
    (time_to_minutes("14:00"), time_to_minutes("14:30")),
]

# Calculate free intervals for each participant in the effective window
raymond_free = get_free_intervals(work_start, work_end, raymond_blocked)
billy_free = get_free_intervals(work_start, work_end, billy_blocked)
donald_free = get_free_intervals(work_start, work_end, donald_blocked)

# Find the common free intervals across all participants
common_free = intersect_intervals(raymond_free, billy_free)
common_free = intersect_intervals(common_free, donald_free)

# Select the first available slot that can accommodate the 30 minute meeting
meeting_slot = find_meeting_slot(common_free, meeting_duration)

if meeting_slot:
    start_minutes, end_minutes = meeting_slot
    meeting_time = f"{minutes_to_time(start_minutes)}:{minutes_to_time(end_minutes)}"
    day_of_week = "Monday"
    print(day_of_week)
    print(meeting_time)
else:
    print("No available slot found.")