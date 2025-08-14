def get_free_intervals(busy_intervals, work_start, work_end):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    prev_end = work_start
    for start, end in sorted_busy:
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

def find_overlap_intervals(intervals1, intervals2):
    i = j = 0
    overlaps = []
    while i < len(intervals1) and j < len(intervals2):
        s1, e1 = intervals1[i]
        s2, e2 = intervals2[j]
        start = max(s1, s2)
        end = min(e1, e2)
        if start < end:
            overlaps.append((start, end))
        if e1 < e2:
            i += 1
        else:
            j += 1
    return overlaps

# Define busy times in minutes
ryan_busy = {
    'Monday': [(570, 600), (660, 720), (780, 810), (930, 960)],
    'Tuesday': [(690, 750), (930, 960)],
    'Wednesday': []
}

adam_busy = {
    'Monday': [(540, 630), (660, 780), (840, 960), (990, 1020)],
    'Tuesday': [(540, 600), (630, 930), (960, 1020)],
    'Wednesday': []
}

work_start = 540  # 9:00 AM
work_end = 1020   # 5:00 PM

days_to_check = ['Tuesday', 'Monday']

for day in days_to_check:
    ryan_free = get_free_intervals(ryan_busy.get(day, []), work_start, work_end)
    adam_free = get_free_intervals(adam_busy.get(day, []), work_start, work_end)
    overlaps = find_overlap_intervals(ryan_free, adam_free)
    for start, end in overlaps:
        if end - start >= 30 * 60:  # 30 minutes
            # Check if it's Monday and before 14:30 (870 minutes)
            if day == 'Monday' and start < 870:
                continue
            # Convert to time format
            start_time = f"{start // 60:02d}:{start % 60:02d}"
            end_time = f"{end // 60:02d}:{end % 60:02d}"
            print(f"{day} {start_time}:{end_time}")
            exit()