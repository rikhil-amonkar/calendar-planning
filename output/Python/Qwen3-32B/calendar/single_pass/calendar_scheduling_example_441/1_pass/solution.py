def subtract_busy_intervals(work_start, work_end, busy_intervals):
    busy_intervals.sort()
    free_intervals = [(work_start, work_end)]
    for start, end in busy_intervals:
        new_free = []
        for (f_start, f_end) in free_intervals:
            if start > f_end or end < f_start:
                new_free.append((f_start, f_end))
            else:
                if f_start < start:
                    new_free.append((f_start, start))
                if f_end > end:
                    new_free.append((end, f_end))
        free_intervals = new_free
    return free_intervals


def intersect_intervals(list1, list2):
    i = 0
    j = 0
    result = []
    while i < len(list1) and j < len(list2):
        a_start, a_end = list1[i]
        b_start, b_end = list2[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            result.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return result


participants = {
    'Joan': [(690, 720), (870, 900)],
    'Megan': [(540, 600), (840, 870), (960, 990)],
    'Austin': [],
    'Betty': [(570, 600), (690, 720), (810, 840), (960, 990)],
    'Judith': [(540, 660), (720, 780), (840, 900)],
    'Terry': [(570, 600), (690, 750), (780, 840), (900, 930), (960, 1020)],
    'Kathryn': [(570, 600), (630, 660), (690, 780), (840, 960), (990, 1020)]
}

work_start = 540  # 9:00 AM in minutes
work_end = 1020   # 5:00 PM in minutes

free_intervals = {}
for name in participants:
    busy = participants[name]
    free = subtract_busy_intervals(work_start, work_end, busy)
    free_intervals[name] = free

# Compute the intersection of all free intervals
current_common = free_intervals[next(iter(participants.keys()))]
for name in participants.keys():
    if name == next(iter(participants.keys())):
        continue
    current_common = intersect_intervals(current_common, free_intervals[name])

# Find the earliest 30-minute slot
earliest_time = None
for interval in current_common:
    start, end = interval
    if end - start >= 30:
        earliest_time = (start, start + 30)
        break


def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"


start_str = to_time_str(earliest_time[0])
end_str = to_time_str(earliest_time[1])
print(f"{start_str}:{end_str} Monday")
