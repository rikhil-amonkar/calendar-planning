def merge_intervals(intervals):
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

def get_free_intervals(merged_busy):
    free = []
    start_work = 9.0
    end_work = 17.0
    prev_end = start_work
    for interval in merged_busy:
        start, end = interval
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < end_work:
        free.append((prev_end, end_work))
    return free

def decimal_to_time(decimal):
    hours = int(decimal)
    minutes = int((decimal - hours) * 60)
    return f"{hours:02d}:{minutes:02d}"

brian = {
    'Monday': [(9.5, 10.0), (12.5, 14.5), (15.5, 16.0)],
    'Tuesday': [(9.0, 9.5)],
    'Wednesday': [(12.5, 14.0), (16.5, 17.0)],
    'Thursday': [(11.0, 11.5), (13.0, 13.5), (16.5, 17.0)],
    'Friday': [(9.5, 10.0), (10.5, 11.0), (13.0, 13.5), (15.0, 16.0), (16.5, 17.0)],
}

julia = {
    'Monday': [(9.0, 10.0), (11.0, 11.5), (12.5, 13.0), (15.5, 16.0)],
    'Tuesday': [(13.0, 14.0), (16.0, 16.5)],
    'Wednesday': [(9.0, 11.5), (12.0, 12.5), (13.0, 17.0)],
    'Thursday': [(9.0, 10.5), (11.0, 17.0)],
    'Friday': [(9.0, 10.0), (10.5, 11.5), (12.5, 14.0), (14.5, 15.0), (15.5, 16.0)],
}

days_order = ['Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Monday']

for day in days_order:
    brian_busy = brian.get(day, [])
    julia_busy = julia.get(day, [])
    combined = brian_busy + julia_busy
    merged = merge_intervals(combined)
    free = get_free_intervals(merged)
    for (s, e) in free:
        if e - s >= 1.0:
            start_time = decimal_to_time(s)
            end_time = decimal_to_time(s + 1.0)
            print(f"{start_time}:{end_time} {day}")
            exit()