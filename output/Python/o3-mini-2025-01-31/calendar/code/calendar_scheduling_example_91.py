from datetime import datetime, timedelta

def time_to_minutes(time_str):
    """Convert HH:MM to minutes since midnight."""
    h, m = map(int, time_str.split(":"))
    return h * 60 + m

def minutes_to_time(minutes):
    """Convert minutes since midnight to HH:MM with leading zero."""
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def invert_intervals(busy_intervals, work_start, work_end):
    """Given busy intervals (in minutes) and work day bounds (in minutes), return free intervals."""
    free_intervals = []
    current = work_start
    for start, end in busy_intervals:
        if current < start:
            free_intervals.append((current, start))
        current = max(current, end)
    if current < work_end:
        free_intervals.append((current, work_end))
    return free_intervals

def intersect_intervals(list1, list2):
    """Intersect two lists of intervals."""
    i, j = 0, 0
    intersection = []
    while i < len(list1) and j < len(list2):
        start1, end1 = list1[i]
        start2, end2 = list2[j]
        # Find overlap if any.
        start_overlap = max(start1, start2)
        end_overlap = min(end1, end2)
        if start_overlap < end_overlap:
            intersection.append((start_overlap, end_overlap))
        # Advance the interval which finishes first.
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersection

# Work day constraints: 9:00 to 17:00
work_start = time_to_minutes("09:00")
work_end   = time_to_minutes("17:00")
meeting_duration = 60  # in minutes

# Busy intervals for each participant (converted to minutes)
# Each tuple is (start_time, end_time)
busy_danielle = [(time_to_minutes("09:00"), time_to_minutes("10:00")),
                 (time_to_minutes("10:30"), time_to_minutes("11:00")),
                 (time_to_minutes("14:30"), time_to_minutes("15:00")),
                 (time_to_minutes("15:30"), time_to_minutes("16:00")),
                 (time_to_minutes("16:30"), time_to_minutes("17:00"))]

busy_bruce = [(time_to_minutes("11:00"), time_to_minutes("11:30")),
              (time_to_minutes("12:30"), time_to_minutes("13:00")),
              (time_to_minutes("14:00"), time_to_minutes("14:30")),
              (time_to_minutes("15:30"), time_to_minutes("16:00"))]

busy_eric = [(time_to_minutes("09:00"), time_to_minutes("09:30")),
             (time_to_minutes("10:00"), time_to_minutes("11:00")),
             (time_to_minutes("11:30"), time_to_minutes("13:00")),
             (time_to_minutes("14:30"), time_to_minutes("15:30"))]

# Compute free intervals for each participant by inverting their busy intervals within work hours.
free_danielle = invert_intervals(busy_danielle, work_start, work_end)
free_bruce = invert_intervals(busy_bruce, work_start, work_end)
free_eric = invert_intervals(busy_eric, work_start, work_end)

# Intersect free intervals of all participants.
common_free = intersect_intervals(free_danielle, free_bruce)
common_free = intersect_intervals(common_free, free_eric)

# Find the first common free interval that is at least as long as the meeting duration.
meeting_start = None
for (start, end) in common_free:
    if end - start >= meeting_duration:
        meeting_start = start
        meeting_end = start + meeting_duration
        break

if meeting_start is not None:
    meeting_time = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
    day_of_week = "Monday"
    print(f"{day_of_week} {meeting_time}")
else:
    print("No available common time slot meeting the requirements.")