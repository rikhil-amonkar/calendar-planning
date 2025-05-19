def parse_time(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def parse_schedule(schedule):
    intervals = []
    for s in schedule:
        start, end = s.split('-')
        intervals.append((parse_time(start), parse_time(end)))
    return intervals

raymond_busy = parse_schedule(['9:00-9:30', '11:30-12:00', '13:00-13:30', '15:00-15:30'])
billy_busy = parse_schedule(['10:00-10:30', '12:00-13:00', '16:30-17:00']) + [(parse_time('15:00'), parse_time('17:00'))]
donald_busy = parse_schedule(['9:00-9:30', '10:00-11:00', '12:00-13:00', '14:00-14:30', '16:00-17:00'])

all_busy = raymond_busy + billy_busy + donald_busy
all_busy.sort()

def merge_intervals(intervals):
    if not intervals:
        return []
    merged = [intervals[0]]
    for current in intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

merged_busy = merge_intervals(all_busy)

work_start = parse_time('9:00')
work_end = parse_time('17:00')

available = []
previous_end = work_start
for start, end in merged_busy:
    if start > previous_end:
        available.append((previous_end, start))
    previous_end = max(previous_end, end)
if previous_end < work_end:
    available.append((previous_end, work_end))

meeting_duration = 30
for slot in available:
    start, end = slot
    if end - start >= meeting_duration:
        latest_end = min(end, parse_time('15:00'))
        if latest_end - start >= meeting_duration:
            proposed_start = start
            proposed_end = start + meeting_duration
            if proposed_end <= parse_time('15:00'):
                print(f"{format_time(proposed_start)}-{format_time(proposed_end)}")
                print("Monday")
                exit()

print("No suitable time found")