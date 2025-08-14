def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_available_intervals(busy_intervals, work_start, work_end):
    busy = sorted(busy_intervals, key=lambda x: x[0])
    merged = []
    for start, end in busy:
        if not merged:
            merged.append((start, end))
        else:
            last_start, last_end = merged[-1]
            if start <= last_end:
                merged[-1] = (last_start, max(last_end, end))
            else:
                merged.append((start, end))
    available = []
    prev_end = work_start
    for start, end in merged:
        if start > prev_end:
            available.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        available.append((prev_end, work_end))
    return available

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

work_start = 9 * 60
work_end = 17 * 60

Danielle_busy = [
    (9*60, 10*60),
    (10*60 + 30, 11*60),
    (14*60 + 30, 15*60),
    (15*60 + 30, 16*60),
    (16*60 + 30, 17*60)
]

Bruce_busy = [
    (11*60, 11*60 + 30),
    (12*60 + 30, 13*60),
    (14*60, 14*60 + 30),
    (15*60 + 30, 16*60)
]

Eric_busy = [
    (9*60, 9*60 + 30),
    (10*60, 11*60),
    (11*60 + 30, 13*60),
    (14*60 + 30, 15*60 + 30)
]

available_d = get_available_intervals(Danielle_busy, work_start, work_end)
available_b = get_available_intervals(Bruce_busy, work_start, work_end)
available_e = get_available_intervals(Eric_busy, work_start, work_end)

common_d_b = intersect_intervals(available_d, available_b)
common_all = intersect_intervals(common_d_b, available_e)

possible_slots = [(start, end) for (start, end) in common_all if end - start >= 60]
selected_slot = possible_slots[0]

start_str = to_time_str(selected_slot[0])
end_str = to_time_str(selected_slot[1])

print(f"{start_str}:{end_str} Monday")