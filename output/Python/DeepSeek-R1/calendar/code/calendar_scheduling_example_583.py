def time_to_min(t_str):
    h, m = map(int, t_str.split(':'))
    return h * 60 + m

def min_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

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

lisa_busy = [
    ('9:00', '9:30'),
    ('10:30', '11:00'),
    ('14:00', '16:00'),
]

anthony_busy = [
    ('9:00', '9:30'),
    ('11:00', '11:30'),
    ('12:30', '13:30'),
    ('14:00', '15:00'),
    ('15:30', '16:00'),
    ('16:30', '17:00'),
]

intervals = []
for start, end in lisa_busy + anthony_busy:
    s = time_to_min(start)
    e = time_to_min(end)
    intervals.append((s, e))

merged = merge_intervals(intervals)
work_start = time_to_min('9:00')
work_end = time_to_min('17:00')

free = []
prev_end = work_start
for start, end in merged:
    if start > prev_end:
        free.append((prev_end, start))
    prev_end = max(prev_end, end)
if prev_end < work_end:
    free.append((prev_end, work_end))

meeting_duration = 30
meeting_start = None
for start, end in free:
    if end - start >= meeting_duration:
        meeting_start = start
        meeting_end = start + meeting_duration
        break

start_str = min_to_time(meeting_start)
end_str = min_to_time(meeting_end)
print(f"Monday {start_str}:{end_str}")