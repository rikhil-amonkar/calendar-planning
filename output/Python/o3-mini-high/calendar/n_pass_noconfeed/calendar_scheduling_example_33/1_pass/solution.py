def time_to_minutes(t):
    # Convert a "HH:MM" string to minutes since midnight.
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    # Convert minutes since midnight into a "HH:MM" string.
    return f"{m // 60:02d}:{m % 60:02d}"

def compute_free_intervals(busy, work_start, work_end):
    # Given a sorted list of busy intervals (in minutes) and the work start/end,
    # compute the free intervals.
    free = []
    current = work_start
    for (start, end) in busy:
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(list1, list2, meeting_duration):
    # Compute the intersection of two lists of intervals.
    result = []
    i, j = 0, 0
    while i < len(list1) and j < len(list2):
        a_start, a_end = list1[i]
        b_start, b_end = list2[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if end - start >= meeting_duration:
            result.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return result

def clip_intervals(intervals, clip_end):
    # Clip each interval so that none extend beyond clip_end.
    clipped = []
    for start, end in intervals:
        if start >= clip_end:
            continue
        new_end = min(end, clip_end)
        if new_end - start > 0:
            clipped.append((start, new_end))
    return clipped

# Meeting parameters
meeting_duration = 30  # in minutes
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
# Bobby would like no meetings after 15:00, so any meeting must finish by then.
bobby_limit = time_to_minutes("15:00")

# Busy schedules for Monday (times are given as HH:MM strings)
lisa_busy_str = [("09:00", "10:00"), ("10:30", "11:30"), ("12:30", "13:00"), ("16:00", "16:30")]
bobby_busy_str = [("09:00", "09:30"), ("10:00", "10:30"), ("11:30", "12:00"), ("15:00", "15:30")]
randy_busy_str = [("09:30", "10:00"), ("10:30", "11:00"), ("11:30", "12:30"),
                  ("13:00", "13:30"), ("14:30", "15:30"), ("16:00", "16:30")]

def convert_schedule(schedule_str):
    return [(time_to_minutes(start), time_to_minutes(end)) for start, end in schedule_str]

lisa_busy = convert_schedule(lisa_busy_str)
bobby_busy = convert_schedule(bobby_busy_str)
randy_busy = convert_schedule(randy_busy_str)

# Compute free intervals for each person during working hours.
lisa_free = compute_free_intervals(sorted(lisa_busy), work_start, work_end)
bobby_free = compute_free_intervals(sorted(bobby_busy), work_start, work_end)
randy_free = compute_free_intervals(sorted(randy_busy), work_start, work_end)

# Apply Bobby’s constraint so that his free intervals do not extend past 15:00.
bobby_free = clip_intervals(bobby_free, bobby_limit)

# First, intersect Lisa’s and Bobby’s free intervals.
common_free = intersect_intervals(lisa_free, bobby_free, meeting_duration)
# Then intersect the result with Randy’s free intervals.
common_free = intersect_intervals(common_free, randy_free, meeting_duration)

# Choose the earliest common free slot that is at least 30 minutes long.
meeting_start = None
for (start, end) in common_free:
    if end - start >= meeting_duration:
        meeting_start = start
        break

if meeting_start is not None:
    meeting_end = meeting_start + meeting_duration
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    # Output the day of the week and time range in the format: HH:MM:HH:MM
    # For example: Monday {13:30:14:00}
    print("Monday", "{" + start_str + ":" + end_str + "}")
else:
    print("No available meeting slot found.")