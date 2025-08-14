WORK_START = 9 * 60
WORK_END = 17 * 60

def get_free_intervals(busy_intervals, work_start, work_end):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    previous_end = work_start
    for start, end in sorted_busy:
        if start > previous_end:
            free.append((previous_end, start))
        previous_end = max(previous_end, end)
    if previous_end < work_end:
        free.append((previous_end, work_end))
    return free

def intersect(a, b):
    i = 0
    j = 0
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

participants_data = [
    [(9*60, 9*60 + 30), (11*60 + 30, 12*60)],
    [(9*60, 9*60 + 30), (12*60, 12*60 + 30), (13*60, 13*60 + 30), (15*60, 16*60), (16*60 + 30, 17*60)],
    [(10*60, 10*60 + 30), (13*60 + 30, 14*60)],
    [(10*60, 11*60), (12*60 + 30, 14*60 + 30)],
    [(9*60 + 30, 11*60), (11*60 + 30, 12*60 + 30), (13*60, 15*60 + 30), (16*60, 17*60)],
    [(9*60, 10*60 + 30), (11*60 + 30, 12*60), (12*60 + 30, 13*60 + 30), (14*60, 17*60)],
    [(9*60, 10*60 + 30), (12*60, 13*60 + 30), (15*60, 15*60 + 30), (16*60, 16*60 + 30)],
]

free_intervals_list = []
for busy_intervals in participants_data:
    free_intervals = get_free_intervals(busy_intervals, WORK_START, WORK_END)
    free_intervals_list.append(free_intervals)

common_free = free_intervals_list[0]
for i in range(1, len(free_intervals_list)):
    common_free = intersect(common_free, free_intervals_list[i])

for interval in common_free:
    start, end = interval
    if end - start >= 30:
        def to_time(minute):
            h = minute // 60
            m = minute % 60
            return f"{h:02d}:{m:02d}"
        start_time = start
        end_time = start + 30
        formatted_time = f"{to_time(start_time)}:{to_time(end_time)}"
        day = "Monday"
        print(f"{{{formatted_time}}} {day}")
        break