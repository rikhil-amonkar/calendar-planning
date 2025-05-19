def parse_time(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def find_meeting_slot(busy_intervals, duration, work_start, work_end):
    merged = []
    for start, end in sorted(busy_intervals):
        if merged and merged[-1][1] >= start:
            merged[-1] = (merged[-1][0], max(merged[-1][1], end))
        else:
            merged.append((start, end))
    
    free = []
    prev_end = work_start
    for start, end in merged:
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    
    for start, end in free:
        if end - start >= duration:
            return (start, start + duration)
    return None

participants = {
    'Ronald': [],
    'Stephen': ['10:00-10:30', '12:00-12:30'],
    'Brittany': ['11:00-11:30', '13:30-14:00', '15:30-16:00', '16:30-17:00'],
    'Dorothy': ['9:00-9:30', '10:00-10:30', '11:00-12:30', '13:00-15:00', '15:30-17:00'],
    'Rebecca': ['9:30-10:30', '11:00-11:30', '12:00-12:30', '13:00-17:00'],
    'Jordan': ['9:00-9:30', '10:00-11:00', '11:30-12:00', '13:00-15:00', '15:30-16:30']
}

busy = []
for person, intervals in participants.items():
    for interval in intervals:
        start_str, end_str = interval.split('-')
        start = parse_time(start_str)
        end = parse_time(end_str)
        busy.append((start, end))

work_start = parse_time('09:00')
work_end = parse_time('17:00')
duration = 30

slot = find_meeting_slot(busy, duration, work_start, work_end)
if slot:
    start, end = slot
    print(f"{to_time_str(start)}-{to_time_str(end)}")
    print("Monday")
else:
    print("No suitable slot found")