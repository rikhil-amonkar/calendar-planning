def minutes_to_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def subtract_busy(working, busy_list):
    free_intervals = []
    current_start = working[0]
    # Sort busy intervals by start time
    for busy in sorted(busy_list):
        busy_start, busy_end = busy
        # If there is a gap before the busy interval, add it
        if busy_start > current_start:
            free_intervals.append((current_start, busy_start))
        # Move current start past the busy interval if needed
        current_start = max(current_start, busy_end)
    # Add any leftover time until end of working hours
    if current_start < working[1]:
        free_intervals.append((current_start, working[1]))
    return free_intervals

def intersect_intervals(list1, list2):
    i, j = 0, 0
    intersections = []
    while i < len(list1) and j < len(list2):
        start1, end1 = list1[i]
        start2, end2 = list2[j]
        # Compute the intersection of the two intervals
        start = max(start1, start2)
        end = min(end1, end2)
        if start < end:
            intersections.append((start, end))
        # Move to the next interval in the list which finishes first
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersections

def find_slot(intersections, duration):
    for interval in intersections:
        start, end = interval
        if end - start >= duration:
            # Return the earliest meeting slot of the required duration
            return (start, start + duration)
    return None

# Define working hours on Monday: 9:00 to 17:00 (in minutes)
work_start = 9 * 60    # 9:00 -> 540 minutes
work_end = 17 * 60     # 17:00 -> 1020 minutes
working_hours = (work_start, work_end)

# James' busy intervals on Monday:
# 11:30 to 12:00  -> (690, 720)
# 14:30 to 15:00  -> (870, 900)
james_busy = [
    (11 * 60 + 30, 12 * 60),
    (14 * 60 + 30, 15 * 60)
]

# John's busy intervals on Monday:
# 9:30 to 11:00   -> (570, 660)
# 11:30 to 12:00  -> (690, 720)
# 12:30 to 13:30  -> (750, 810)
# 14:30 to 16:30  -> (870, 990)
john_busy = [
    (9 * 60 + 30, 11 * 60),
    (11 * 60 + 30, 12 * 60),
    (12 * 60 + 30, 13 * 60 + 30),
    (14 * 60 + 30, 16 * 60 + 30)
]

# Compute free intervals for each person
james_free = subtract_busy(working_hours, james_busy)
john_free = subtract_busy(working_hours, john_busy)

# Compute common free intervals (intersection)
common_free = intersect_intervals(james_free, john_free)

# Required meeting duration in minutes (1 hour)
meeting_duration = 60

slot = find_slot(common_free, meeting_duration)

if slot:
    start, end = slot
    meeting_time = f"{minutes_to_str(start)}:{minutes_to_str(end)}"
    print(f"Monday {meeting_time}")
else:
    print("No available slot found")