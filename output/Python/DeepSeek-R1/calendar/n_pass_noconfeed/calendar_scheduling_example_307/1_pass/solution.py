def time_to_minutes(time_str):
    h, m = time_str.split(':')
    return (int(h) - 9) * 60 + int(m)

def minutes_to_time(mins):
    total_minutes = mins
    hours = 9 + total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

participants = {
    'Ronald': [],
    'Stephen': [('10:00','10:30'), ('12:00','12:30')],
    'Brittany': [('11:00','11:30'), ('13:30','14:00'), ('15:30','16:00'), ('16:30','17:00')],
    'Dorothy': [('9:00','9:30'), ('10:00','10:30'), ('11:00','12:30'), ('13:00','15:00'), ('15:30','17:00')],
    'Rebecca': [('9:30','10:30'), ('11:00','11:30'), ('12:00','12:30'), ('13:00','17:00')],
    'Jordan': [('9:00','9:30'), ('10:00','11:00'), ('11:30','12:00'), ('13:00','15:00'), ('15:30','16:30')]
}

busy_intervals = []
for person, intervals in participants.items():
    for interval in intervals:
        start_min = time_to_minutes(interval[0])
        end_min = time_to_minutes(interval[1])
        busy_intervals.append((start_min, end_min))

if not busy_intervals:
    meeting_start = 0
    meeting_end = 30
else:
    busy_intervals.sort(key=lambda x: x[0])
    merged = []
    start_curr, end_curr = busy_intervals[0]
    for i in range(1, len(busy_intervals)):
        s, e = busy_intervals[i]
        if s <= end_curr:
            end_curr = max(end_curr, e)
        else:
            merged.append((start_curr, end_curr))
            start_curr, end_curr = s, e
    merged.append((start_curr, end_curr))
    
    free_intervals = []
    if merged[0][0] > 0:
        free_intervals.append((0, merged[0][0]))
    for i in range(1, len(merged)):
        prev_end = merged[i-1][1]
        curr_start = merged[i][0]
        if curr_start > prev_end:
            free_intervals.append((prev_end, curr_start))
    if merged[-1][1] < 480:
        free_intervals.append((merged[-1][1], 480))
    
    meeting_start = None
    for start, end in free_intervals:
        if end - start >= 30:
            meeting_start = start
            break
    if meeting_start is None:
        meeting_start = 0
    meeting_end = meeting_start + 30

start_time_str = minutes_to_time(meeting_start)
end_time_str = minutes_to_time(meeting_end)
time_range_str = f"{start_time_str}:{end_time_str}"

print("Monday")
print(time_range_str)