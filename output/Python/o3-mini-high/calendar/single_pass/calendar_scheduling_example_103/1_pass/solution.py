def minutes_to_time(m):
    """Convert minutes since midnight to HH:MM format."""
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def get_free_intervals(busy, work_start, work_end):
    """Given a list of busy intervals and working hours, return free intervals."""
    busy_sorted = sorted(busy, key=lambda x: x[0])
    free = []
    current = work_start
    for b_start, b_end in busy_sorted:
        if b_start > current:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(list1, list2):
    """Intersect two lists of intervals."""
    i, j = 0, 0
    intersection = []
    while i < len(list1) and j < len(list2):
        start = max(list1[i][0], list2[j][0])
        end = min(list1[i][1], list2[j][1])
        if start < end:
            intersection.append((start, end))
        # Move to the next interval in the list that ends earlier.
        if list1[i][1] < list2[j][1]:
            i += 1
        else:
            j += 1
    return intersection

# Meeting duration in minutes
meeting_duration = 30

# Working hours on Monday: 9:00 (540 minutes) to 17:00 (1020 minutes)
work_start = 9 * 60
work_end = 17 * 60

# Busy intervals for each participant in minutes (start, end)
# Times are converted: HH:MM -> minutes.
# Diane: 9:30-10:00, 14:30-15:00
# Jack: 13:30-14:00, 14:30-15:00
# Eugene: 9:00-10:00, 10:30-11:30, 12:00-14:30, 15:00-16:30
# Patricia: 9:30-10:30, 11:00-12:00, 12:30-14:00, 15:00-16:30
schedules = {
    "Diane": [(9*60+30, 10*60+0), (14*60+30, 15*60+0)],
    "Jack": [(13*60+30, 14*60+0), (14*60+30, 15*60+0)],
    "Eugene": [(9*60+0, 10*60+0), (10*60+30, 11*60+30), (12*60+0, 14*60+30), (15*60+0, 16*60+30)],
    "Patricia": [(9*60+30, 10*60+30), (11*60+0, 12*60+0), (12*60+30, 14*60+0), (15*60+0, 16*60+30)]
}

# Calculate free intervals for each participant during working hours
free_times = {}
for person, busy in schedules.items():
    free_times[person] = get_free_intervals(busy, work_start, work_end)

# Find common free intervals across all participants
common_free = None
for free in free_times.values():
    if common_free is None:
        common_free = free
    else:
        common_free = intersect_intervals(common_free, free)

# Select the first interval that can accommodate the meeting duration.
selected = None
for start, end in common_free:
    if end - start >= meeting_duration:
        selected = (start, start + meeting_duration)
        break

if selected:
    start_str = minutes_to_time(selected[0])
    end_str = minutes_to_time(selected[1])
    # Output the meeting time and day.
    print("Monday")
    print(f"{start_str}:{end_str}")
else:
    print("No available slot found.")