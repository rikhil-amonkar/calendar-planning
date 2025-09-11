def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

participants = {
    'Andrea': [('09:30', '10:30'), ('13:30', '14:30')],
    'Ruth': [('12:30', '13:00'), ('15:00', '15:30')],
    'Steven': [('10:00', '10:30'), ('11:00', '11:30'), ('12:00', '12:30'), ('13:30', '14:00'), ('15:00', '16:00')],
    'Grace': [],
    'Kyle': [('09:00', '09:30'), ('10:30', '12:00'), ('12:30', '13:00'), ('13:30', '15:00'), ('15:30', '16:00'), ('16:30', '17:00')],
    'Elijah': [('09:00', '11:00'), ('11:30', '13:00'), ('13:30', '14:00'), ('15:30', '16:00'), ('16:30', '17:00')],
    'Lori': [('09:00', '09:30'), ('10:00', '11:30'), ('12:00', '13:30'), ('14:00', '16:00'), ('16:30', '17:00')],
}

work_start = 9 * 60  # 540 minutes
work_end = 17 * 60   # 1020 minutes

all_merged_busy = {}

for name, busy_times in participants.items():
    intervals = []
    for start_str, end_str in busy_times:
        start = time_to_minutes(start_str)
        end = time_to_minutes(end_str)
        # Clip to work hours
        start_clipped = max(start, work_start)
        end_clipped = min(end, work_end)
        if start_clipped < end_clipped:
            intervals.append((start_clipped, end_clipped))
    # Sort intervals by start time
    intervals.sort()
    # Merge overlapping intervals
    merged = []
    for interval in intervals:
        if not merged:
            merged.append(interval)
        else:
            last = merged[-1]
            if interval[0] <= last[1]:  # Overlapping or adjacent
                # Merge
                new_start = last[0]
                new_end = max(last[1], interval[1])
                merged[-1] = (new_start, new_end)
            else:
                merged.append(interval)
    all_merged_busy[name] = merged

# Now iterate through all possible start times
for start in range(work_start, work_end - 30 + 1):
    end = start + 30
    valid = True
    for name, busy_intervals in all_merged_busy.items():
        for (b_start, b_end) in busy_intervals:
            if start < b_end and end > b_start:
                valid = False
                break
        if not valid:
            break
    if valid:
        start_time = minutes_to_time(start)
        end_time = minutes_to_time(end)
        print(f"{start_time}:{end_time} Monday")
        exit()