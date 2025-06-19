def time_str_to_minutes(time_str):
    h, m = time_str.split(':')
    return int(h) * 60 + int(m)

def minutes_to_time_str(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def subtract_busy(work_interval, busy_list):
    free_intervals = [work_interval]
    if not busy_list:
        return free_intervals
    busy_list_sorted = sorted(busy_list, key=lambda x: x[0])
    for busy in busy_list_sorted:
        new_free = []
        for interval in free_intervals:
            if busy[1] <= interval[0] or busy[0] >= interval[1]:
                new_free.append(interval)
            else:
                if interval[0] < busy[0]:
                    new_free.append((interval[0], busy[0]))
                if busy[1] < interval[1]:
                    new_free.append((busy[1], interval[1]))
        free_intervals = new_free
    return free_intervals

def intersect_intervals(intervals1, intervals2):
    i = j = 0
    common = []
    while i < len(intervals1) and j < len(intervals2):
        a = intervals1[i]
        b = intervals2[j]
        low = max(a[0], b[0])
        high = min(a[1], b[1])
        if low < high:
            common.append((low, high))
        if a[1] < b[1]:
            i += 1
        else:
            j += 1
    return common

work_start_min = 9 * 60
work_end_min = 17 * 60

robert_busy = {
    'Monday': [("11:00", "11:30"), ("14:00", "14:30"), ("15:30", "16:00")],
    'Tuesday': [("10:30", "11:00"), ("15:00", "15:30")],
    'Wednesday': [("10:00", "11:00"), ("11:30", "12:00"), ("12:30", "13:00"), ("13:30", "14:00"), ("15:00", "15:30"), ("16:00", "16:30")]
}

ralph_busy = {
    'Monday': [("10:00", "13:30"), ("14:00", "14:30"), ("15:00", "17:00")],
    'Tuesday': [("9:00", "9:30"), ("10:00", "10:30"), ("11:00", "11:30"), ("12:00", "13:00"), ("14:00", "15:30"), ("16:00", "17:00")],
    'Wednesday': [("10:30", "11:00"), ("11:30", "12:00"), ("13:00", "14:30"), ("16:30", "17:00")]
}

candidates = []

days = ['Monday', 'Tuesday', 'Wednesday']
for day in days:
    rb_list = []
    for s, e in robert_busy[day]:
        s_min = time_str_to_minutes(s)
        e_min = time_str_to_minutes(e)
        rb_list.append((s_min, e_min))
    rb_list.sort(key=lambda x: x[0])
    
    rl_list = []
    for s, e in ralph_busy[day]:
        s_min = time_str_to_minutes(s)
        e_min = time_str_to_minutes(e)
        rl_list.append((s_min, e_min))
    rl_list.sort(key=lambda x: x[0])
    
    free_robert = subtract_busy((work_start_min, work_end_min), rb_list)
    free_ralph = subtract_busy((work_start_min, work_end_min), rl_list)
    
    common_free = intersect_intervals(free_robert, free_ralph)
    
    for start, end in common_free:
        duration = end - start
        if duration >= 30:
            candidates.append((day, start))

non_monday_candidates = [c for c in candidates if c[0] in ['Tuesday', 'Wednesday']]
if non_monday_candidates:
    candidates_to_choose = non_monday_candidates
else:
    candidates_to_choose = [c for c in candidates if c[0] == 'Monday']

day_index_map = {'Monday': 0, 'Tuesday': 1, 'Wednesday': 2}
candidates_with_index = []
for day, start in candidates_to_choose:
    idx = day_index_map[day]
    candidates_with_index.append((idx, start, day, start))

candidates_with_index.sort(key=lambda x: (x[0], x[1]))

if candidates_with_index:
    chosen_idx, chosen_start, chosen_day, _ = candidates_with_index[0]
    meeting_end_minutes = chosen_start + 30
    start_h = chosen_start // 60
    start_m = chosen_start % 60
    end_h = meeting_end_minutes // 60
    end_m = meeting_end_minutes % 60
    time_output = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
    print(chosen_day)
    print(time_output)
else:
    print("No solution found")