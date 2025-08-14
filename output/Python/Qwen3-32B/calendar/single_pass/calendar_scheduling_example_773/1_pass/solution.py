def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

busy_times = {
    'Monday': [
        (600, 690),
        (720, 780),
        (840, 870),
        (900, 1020)
    ],
    'Tuesday': [
        (630, 690),
        (720, 870),
        (900, 930),
        (960, 1020)
    ],
    'Wednesday': [
        (570, 690),
        (750, 840),
        (870, 930),
        (990, 1020)
    ]
}

possible_slots = []

for day in ['Monday', 'Tuesday', 'Wednesday']:
    work_start = 540
    work_end = 1020
    free_intervals = [(work_start, work_end)]
    busy_list = sorted(busy_times[day], key=lambda x: x[0])
    for busy in busy_list:
        new_free = []
        for (fs, fe) in free_intervals:
            if busy[1] <= fs:
                new_free.append((fs, fe))
                continue
            if busy[0] >= fe:
                new_free.append((fs, fe))
                continue
            left_start = fs
            left_end = busy[0]
            if left_start < left_end:
                new_free.append((left_start, left_end))
            right_start = busy[1]
            right_end = fe
            if right_start < right_end:
                new_free.append((right_start, right_end))
        free_intervals = new_free
    for (fs, fe) in free_intervals:
        if fe - fs >= 60:
            possible_slots.append((day, fs, fe))

possible_slots.sort(key=lambda x: (['Monday', 'Tuesday', 'Wednesday'].index(x[0]), x[1]))

if possible_slots:
    earliest_day, earliest_start, earliest_end = possible_slots[0]
    start_str = to_time_str(earliest_start)
    end_str = to_time_str(earliest_end)
    print(f"{start_str}:{end_str} {earliest_day}")
else:
    print("No available slot found")