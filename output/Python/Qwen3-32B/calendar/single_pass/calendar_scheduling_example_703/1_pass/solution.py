def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current = work_start
    for start, end in sorted_busy:
        if current < start:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def compute_overlap(intervals1, intervals2):
    i = 0
    j = 0
    overlap = []
    while i < len(intervals1) and j < len(intervals2):
        s_start, s_end = intervals1[i]
        b_start, b_end = intervals2[j]
        start = max(s_start, b_start)
        end = min(s_end, b_end)
        if start < end:
            overlap.append((start, end))
        if s_end < b_end:
            i += 1
        else:
            j += 1
    return overlap

def find_meeting_time():
    stephanie_busy = {
        'Monday': [(570, 600), (630, 660), (690, 720), (840, 870)],
        'Tuesday': [(720, 780)],
        'Wednesday': [(540, 600), (780, 840)],
    }
    betty_busy = {
        'Monday': [(540, 600), (660, 690), (870, 900), (930, 960)],
        'Tuesday': [(540, 570), (690, 720), (750, 870), (930, 960)],
        'Wednesday': [(600, 690), (720, 840), (870, 1020)],
    }
    work_start = 540
    work_end = 1020
    days_order = ['Tuesday', 'Wednesday', 'Monday']

    for day in days_order:
        if day == 'Tuesday':
            max_end = 750
        else:
            max_end = work_end
        s_free = get_free_intervals(stephanie_busy.get(day, []), work_start, work_end)
        b_free = get_free_intervals(betty_busy.get(day, []), work_start, work_end)
        overlaps = compute_overlap(s_free, b_free)
        for start, end in overlaps:
            adjusted_end = min(end, max_end)
            if adjusted_end - start >= 60:
                meeting_start = start
                meeting_end = meeting_start + 60
                start_time = minutes_to_time(meeting_start)
                end_time = minutes_to_time(meeting_end)
                return f"{start_time}:{end_time} {day}"
    return "No solution found"

print(find_meeting_time())