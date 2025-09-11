def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    busy_intervals.sort()
    free_intervals = []
    prev_end = work_start
    for start, end in busy_intervals:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free_intervals.append((prev_end, work_end))
    return free_intervals

def find_overlapping_intervals(intervals1, intervals2):
    i = 0
    j = 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        a_start, a_end = intervals1[i]
        b_start, b_end = intervals2[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            result.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return result

# Define work hours in minutes
work_start = 9 * 60
work_end = 17 * 60

# Michael's busy intervals
busy_michael = [(9*60 + 30, 10*60 + 30), (15*60, 15*60 + 30), (16*60, 16*60 + 30)]

# Arthur's busy intervals
busy_arthur = [(9*60, 12*60), (13*60, 15*60), (15*60 + 30, 16*60), (16*60 + 30, 17*60)]

# Generate free intervals for Michael and Arthur
free_michael = get_free_intervals(busy_michael, work_start, work_end)
free_arthur = get_free_intervals(busy_arthur, work_start, work_end)

# Find overlapping intervals between Michael and Arthur
overlapping = find_overlapping_intervals(free_michael, free_arthur)

# Now check for a 30-minute slot
for interval in overlapping:
    start, end = interval
    duration = end - start
    if duration >= 30:
        # Pick earliest possible 30-minute slot
        meeting_start = start
        meeting_end = start + 30
        # Convert to time strings
        start_time = minutes_to_time(meeting_start)
        end_time = minutes_to_time(meeting_end)
        day = "Monday"
        print(f"{start_time}:{end_time} {day}")
        break