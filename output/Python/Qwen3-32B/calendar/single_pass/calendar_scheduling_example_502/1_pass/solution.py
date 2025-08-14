def generate_free_intervals(busy_intervals, work_start, work_end):
    busy_intervals.sort()
    free_intervals = []
    prev_end = work_start
    for start, end in busy_intervals:
        if prev_end < start:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free_intervals.append((prev_end, work_end))
    return free_intervals

def find_overlapping_intervals(free1, free2):
    overlapping = []
    i = j = 0
    while i < len(free1) and j < len(free2):
        a_start, a_end = free1[i]
        b_start, b_end = free2[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            overlapping.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return overlapping

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

work_start = 540  # 9:00 AM
work_end = 1020   # 5:00 PM

# Jack's busy intervals
jack_buses = [(570, 630), (660, 690), (750, 780), (840, 870), (960, 990)]
# Charlotte's busy intervals
charlotte_buses = [(570, 600), (630, 720), (750, 810), (840, 960)]

jack_free = generate_free_intervals(jack_buses, work_start, work_end)
charlotte_free = generate_free_intervals(charlotte_buses, work_start, work_end)

overlapping = find_overlapping_intervals(jack_free, charlotte_free)

valid_intervals = []
for interval in overlapping:
    start, end = interval
    duration = end - start
    if duration >= 30 and end <= 750:  # 750 is 12:30 PM
        valid_intervals.append(interval)

if valid_intervals:
    earliest = min(valid_intervals, key=lambda x: x[0])
    start_time = earliest[0]
    end_time = start_time + 30
    start_str = to_time_str(start_time)
    end_str = to_time_str(end_time)
    print(f"{{ {start_str}:{end_str} }} Monday")
else:
    print("No suitable time found")