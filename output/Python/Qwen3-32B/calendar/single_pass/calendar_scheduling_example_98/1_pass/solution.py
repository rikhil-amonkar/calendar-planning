def time_str_to_min(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m


def min_to_time_str(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"


def process_participant(participant):
    work_start = 9 * 60
    work_end = participant['work_end']
    busy_intervals = []
    for interval in participant['busy']:
        start_str, end_str = interval.split('-')
        start = time_str_to_min(start_str)
        end = time_str_to_min(end_str)
        busy_intervals.append((start, end))

    # Sort and merge busy intervals
    if not busy_intervals:
        busy_intervals = []
    else:
        busy_intervals.sort()
        merged = []
        current_start, current_end = busy_intervals[0]
        for start, end in busy_intervals[1:]:
            if start <= current_end:
                current_end = max(current_end, end)
            else:
                merged.append((current_start, current_end))
                current_start, current_end = start, end
        merged.append((current_start, current_end))
        busy_intervals = merged

    # Compute available intervals
    available = []
    prev_end = work_start
    for start, end in busy_intervals:
        if start > prev_end:
            available.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        available.append((prev_end, work_end))
    return available


def interval_intersection(a, b):
    i = 0
    j = 0
    res = []
    while i < len(a) and j < len(b):
        a_start, a_end = a[i]
        b_start, b_end = b[j]
        # calculate overlap
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            res.append((start, end))
        # move pointer
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return res


participants = [
    {
        'name': 'Juan',
        'busy': ['9:00-10:30', '15:30-16:00'],
        'work_end': 16 * 60  # 960
    },
    {
        'name': 'Marilyn',
        'busy': ['11:00-11:30', '12:30-13:00'],
        'work_end': 17 * 60  # 1020
    },
    {
        'name': 'Ronald',
        'busy': ['9:00-10:30', '12:00-12:30', '13:00-13:30', '14:00-16:30'],
        'work_end': 17 * 60  # 1020
    }
]

# Compute available intervals for each participant
available_juan = process_participant(participants[0])
available_marilyn = process_participant(participants[1])
available_ronald = process_participant(participants[2])

# Find intersection between Juan and Marilyn
common_available = interval_intersection(available_juan, available_marilyn)

# Find intersection with Ronald
common_available = interval_intersection(common_available, available_ronald)

# Now find the first interval in common_available with length >= meeting duration (30)
meeting_duration = 30
for start, end in common_available:
    if end - start >= meeting_duration:
        # pick the first one
        proposed_start = start
        proposed_end = start + meeting_duration
        day = "Monday"
        # output in the required format
        start_time = min_to_time_str(proposed_start)
        end_time = min_to_time_str(proposed_end)
        print(f"{{{start_time}:{end_time}}} {day}")
        break
