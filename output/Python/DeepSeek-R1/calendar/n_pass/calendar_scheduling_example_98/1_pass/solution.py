def get_free_intervals(busy_intervals, work_start, work_end):
    if not busy_intervals:
        return [(work_start, work_end)]
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current_start = work_start
    for s, e in sorted_busy:
        if current_start < s:
            free.append((current_start, s))
        current_start = max(current_start, e)
    if current_start < work_end:
        free.append((current_start, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    i = j = 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        low = max(intervals1[i][0], intervals2[j][0])
        high = min(intervals1[i][1], intervals2[j][1])
        if low < high:
            result.append((low, high))
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return result

def min_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Work hours: 9:00 to 17:00 (in minutes from midnight)
work_start = 9 * 60  # 540 minutes
work_end = 17 * 60   # 1020 minutes

# Busy intervals for each participant (in minutes from midnight)
juan_busy = [(9*60, 10*60+30), (15*60+30, 16*60)]
marilyn_busy = [(11*60, 11*60+30), (12*60+30, 13*60)]
ronald_busy = [(9*60, 10*60+30), (12*60, 12*60+30), (13*60, 13*60+30), (14*60, 16*60+30)]

# Juan cannot meet after 16:00, so adjust his work_end to 16:00 (960 minutes)
free_juan = get_free_intervals(juan_busy, work_start, 16*60)
free_marilyn = get_free_intervals(marilyn_busy, work_start, work_end)
free_ronald = get_free_intervals(ronald_busy, work_start, work_end)

# Find common free intervals
common = intersect_intervals(free_juan, free_marilyn)
common = intersect_intervals(common, free_ronald)

# Meeting duration in minutes
duration = 30
meeting_start = None
meeting_end = None

# Find the first available slot of at least 'duration' minutes
for start, end in common:
    if end - start >= duration:
        meeting_start = start
        meeting_end = start + duration
        break

if meeting_start is not None:
    start_str = min_to_time(meeting_start)
    end_str = min_to_time(meeting_end)
    print(f"{start_str}:{end_str}")
    print("Monday")
else:
    print("No suitable time found")