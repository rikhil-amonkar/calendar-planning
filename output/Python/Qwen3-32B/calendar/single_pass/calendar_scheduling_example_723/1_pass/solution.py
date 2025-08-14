def get_free_times(busy_intervals, work_start=540, work_end=1020):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current_start = work_start
    for start, end in sorted_busy:
        if current_start < start:
            free.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < work_end:
        free.append((current_start, work_end))
    return free

def find_overlaps(list1, list2):
    i = 0
    j = 0
    overlaps = []
    while i < len(list1) and j < len(list2):
        a_start, a_end = list1[i]
        b_start, b_end = list2[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            overlaps.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return overlaps

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Busy times for Arthur and Michael
arthur_busy = {
    'Monday': [(11*60, 11*60 + 30), (13*60 + 30, 14*60), (15*60, 15*60 + 30)],
    'Tuesday': [(13*60, 13*60 + 30), (16*60, 16*60 + 30)],
    'Wednesday': [(10*60, 10*60 + 30), (11*60, 11*60 + 30), (12*60, 12*60 + 30), (14*60, 14*60 + 30), (16*60, 16*60 + 30)],
}

michael_busy = {
    'Monday': [(9*60, 12*60), (12*60 + 30, 13*60), (14*60, 14*60 + 30), (15*60, 17*60)],
    'Tuesday': [(9*60 + 30, 11*60 + 30), (12*60, 13*60 + 30), (14*60, 15*60 + 30)],
    'Wednesday': [(10*60, 12*60 + 30), (13*60, 13*60 + 30)],
}

# Days to check in order
days_order = ['Monday', 'Tuesday', 'Wednesday']
meeting_duration = 30  # in minutes

for day in days_order:
    if day == 'Tuesday':
        continue
    arthur_day_busy = arthur_busy.get(day, [])
    michael_day_busy = michael_busy.get(day, [])
    arthur_free = get_free_times(arthur_day_busy)
    michael_free = get_free_times(michael_day_busy)
    overlaps = find_overlaps(arthur_free, michael_free)
    for start, end in overlaps:
        if end - start >= meeting_duration:
            start_str = to_time_str(start)
            end_str = to_time_str(start + meeting_duration)
            print(f"{start_str}:{end_str} {day}")
            exit()

print("No suitable time found")