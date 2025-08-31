def generate_available(busy_intervals, work_start, work_end):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    available = []
    prev_end = work_start
    for start, end in sorted_busy:
        if start > prev_end:
            available.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        available.append((prev_end, work_end))
    return available


def interval_intersection(list1, list2):
    i = j = 0
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


def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"


work_day_start = 9 * 60
work_day_end = 17 * 60

participants = [
    {'name': 'Andrea', 'busy': []},
    {'name': 'Jack', 'busy': [(540, 570), (840, 870)]},
    {'name': 'Madison', 'busy': [(570, 630), (780, 840), (900, 930), (990, 1020)]},
    {'name': 'Rachel', 'busy': [(570, 630), (660, 690), (720, 810), (870, 930), (960, 1020)]},
    {'name': 'Douglas', 'busy': [(540, 690), (720, 990)]},
    {'name': 'Ryan', 'busy': [(540, 570), (780, 840), (870, 1020)]}
]

global_available = [(work_day_start, work_day_end)]

for participant in participants:
    busy_intervals = participant['busy']
    available = generate_available(busy_intervals, work_day_start, work_day_end)
    global_available = interval_intersection(global_available, available)

meeting_start = None
meeting_end = None
for interval in global_available:
    start_time, end_time = interval
    if end_time - start_time >= 30:
        meeting_start = start_time
        meeting_end = start_time + 30
        break

start_str = minutes_to_time(meeting_start)
end_str = minutes_to_time(meeting_end)
day = "Monday"

print(f"{start_str}:{end_str} {day}")
