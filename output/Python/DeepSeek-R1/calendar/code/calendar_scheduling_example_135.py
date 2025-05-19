def time_to_min(t):
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def min_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

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

def get_free_intervals(busy_intervals, work_start, work_end):
    merged_busy = merge_intervals(busy_intervals)
    free = []
    previous_end = work_start
    for start, end in merged_busy:
        if start > previous_end:
            free.append((previous_end, start))
        previous_end = max(previous_end, end)
    if previous_end < work_end:
        free.append((previous_end, work_end))
    return free

def intersect_intervals(a, b):
    i = j = 0
    result = []
    while i < len(a) and j < len(b):
        a_start, a_end = a[i]
        b_start, b_end = b[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            result.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return result

# Define work hours
work_start = time_to_min('09:00')
work_end = time_to_min('17:00')

# Define participant busy intervals
eric_busy = []
ashley_busy = [('10:00', '10:30'), ('11:00', '12:00'), ('12:30', '13:00'), ('15:00', '16:00')]
ronald_busy = [('09:00', '09:30'), ('10:00', '11:30'), ('12:30', '14:00'), ('14:30', '17:00')]
larry_busy = [('09:00', '12:00'), ('13:00', '17:00')]

# Convert to minutes
def parse_busy(busy_list):
    return [(time_to_min(s), time_to_min(e)) for s, e in busy_list]

eric_free = get_free_intervals(parse_busy(eric_busy), work_start, work_end)
ashley_free = get_free_intervals(parse_busy(ashley_busy), work_start, work_end)
ronald_free = get_free_intervals(parse_busy(ronald_busy), work_start, work_end)
larry_free = get_free_intervals(parse_busy(larry_busy), work_start, work_end)

# Find intersection
current = eric_free
current = intersect_intervals(current, ashley_free)
current = intersect_intervals(current, ronald_free)
current = intersect_intervals(current, larry_free)

# Find first 30-minute slot
for start, end in current:
    if end - start >= 30:
        print(f"{min_to_time(start)}:{min_to_time(start + 30)}")
        print("Monday")
        exit()

print("No suitable time found.")