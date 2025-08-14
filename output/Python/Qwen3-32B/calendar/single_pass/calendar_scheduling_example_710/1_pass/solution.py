def minutes_to_time_str(m):
    hours = m // 60
    mins = m % 60
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

def interval_intersection(list1, list2):
    i = 0
    j = 0
    res = []
    while i < len(list1) and j < len(list2):
        a_start, a_end = list1[i]
        b_start, b_end = list2[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            res.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return res

participants = {
    'Cheryl': {
        'Monday': [(9*60, 9*60+30), (11*60+30, 13*60), (15*60+30, 16*60)],
        'Tuesday': [(15*60, 15*60+30)],
        'Wednesday': []
    },
    'Kyle': {
        'Monday': [(9*60, 17*60)],
        'Tuesday': [(9*60+30, 17*60)],
        'Wednesday': [(9*60, 9*60+30), (10*60, 13*60), (13*60+30, 14*60), (14*60+30, 17*60)]
    }
}

for day in ['Monday', 'Tuesday']:
    cheryl_buses = participants['Cheryl'][day]
    kyle_buses = participants['Kyle'][day]
    cheryl_free = get_free_intervals(cheryl_buses, 9*60, 17*60)
    kyle_free = get_free_intervals(kyle_buses, 9*60, 17*60)
    common = interval_intersection(cheryl_free, kyle_free)
    for start, end in common:
        if end - start >= 30:
            start_str = minutes_to_time_str(start)
            end_str = minutes_to_time_str(end)
            print(f"{start_str}:{end_str} {day}")
            break