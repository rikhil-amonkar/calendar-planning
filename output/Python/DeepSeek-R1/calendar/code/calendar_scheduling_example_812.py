def find_meeting_time():
    work_start = 540  # 9:00 in minutes
    work_end = 1020   # 17:00 in minutes

    mary_schedule = {
        'Monday': [],
        'Tuesday': [(600, 630), (930, 960)],
        'Wednesday': [(570, 600), (900, 930)],
        'Thursday': [(540, 600), (630, 690)]
    }

    alexis_schedule = {
        'Monday': [(540, 600), (630, 720), (750, 990)],
        'Tuesday': [(540, 600), (630, 690), (720, 930), (960, 1020)],
        'Wednesday': [(540, 660), (690, 1020)],
        'Thursday': [(600, 720), (840, 870), (930, 960), (990, 1020)]
    }

    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']

    for day in days:
        intervals = []
        intervals.extend(mary_schedule[day])
        intervals.extend(alexis_schedule[day])
        merged = merge(intervals)
        available = find_available_slots(merged, work_start, work_end)
        for slot in available:
            start, end = slot
            if end - start >= 30:
                start_time = f"{start//60:02d}:{start%60:02d}"
                end_time = f"{end//60:02d}:{end%60:02d}"
                print(f"{day}:{start_time}:{end_time}")
                return

    print("No suitable time found")

def merge(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = [sorted_intervals[0]]
    for current in sorted_intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

def find_available_slots(merged, work_start, work_end):
    available = []
    prev_end = work_start
    for start, end in merged:
        if start > prev_end:
            available.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        available.append((prev_end, work_end))
    return available

find_meeting_time()