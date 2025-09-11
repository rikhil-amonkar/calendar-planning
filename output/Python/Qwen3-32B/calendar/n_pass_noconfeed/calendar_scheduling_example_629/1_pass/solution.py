def get_free_intervals(work_start, work_end, busy_intervals):
    sorted_buses = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current_start = work_start
    for start, end in sorted_buses:
        if current_start < start:
            free.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < work_end:
        free.append((current_start, work_end))
    return free

def to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

participants = {
    'Margaret': {
        'Tuesday': [(12 * 60, 12 * 60 + 30)],  # 12:00-12:30
        'constraints': {
            'start_after': 14 * 60 + 30  # 14:30
        }
    },
    'Alexis': {
        'Tuesday': [(9 * 60, 9 * 60 + 30), (10 * 60, 10 * 60 + 30), (14 * 60, 16 * 60 + 30)]
    }
}

work_start = 9 * 60
work_end = 17 * 60
meeting_duration = 30  # minutes

day = 'Tuesday'

free_intervals = []

for name in participants:
    participant = participants[name]
    if day not in participant:
        continue
    busy_intervals = participant[day]
    free = get_free_intervals(work_start, work_end, busy_intervals)
    constraints = participant.get('constraints', {})
    if 'start_after' in constraints:
        start_after = constraints['start_after']
        adjusted = []
        for (s, e) in free:
            new_s = max(s, start_after)
            if new_s < e:
                adjusted.append((new_s, e))
        free = adjusted
    free_intervals.append(free)

p1_free = free_intervals[0]
p2_free = free_intervals[1]

i = 0
j = 0
overlapping = []
while i < len(p1_free) and j < len(p2_free):
    s1, e1 = p1_free[i]
    s2, e2 = p2_free[j]
    start = max(s1, s2)
    end = min(e1, e2)
    if start < end:
        overlapping.append((start, end))
    if e1 < e2:
        i += 1
    else:
        j += 1

for interval in overlapping:
    start, end = interval
    if end - start >= meeting_duration:
        start_time = to_time(start)
        end_time = to_time(start + meeting_duration)
        print(f"{day} {start_time}:{end_time}")
        break