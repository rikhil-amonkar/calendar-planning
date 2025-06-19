def time_to_minutes(time_str):
    h, m = time_str.split(':')
    return int(h) * 60 + int(m)

def minutes_to_time_str(total_minutes):
    h = total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

# Define work hours and meeting duration
work_start = time_to_minutes('9:00')
work_end = time_to_minutes('17:00')
meeting_duration = 30  # minutes

# List to collect all busy intervals
busy_intervals = []

# Add busy intervals for Doris
busy_intervals.append([time_to_minutes('9:00'), time_to_minutes('11:00')])
busy_intervals.append([time_to_minutes('13:30'), time_to_minutes('14:00')])
busy_intervals.append([time_to_minutes('16:00'), time_to_minutes('16:30')])

# Add busy intervals for Theresa
busy_intervals.append([time_to_minutes('10:00'), time_to_minutes('12:00')])

# Add busy intervals for Terry
busy_intervals.append([time_to_minutes('9:30'), time_to_minutes('10:00')])
busy_intervals.append([time_to_minutes('11:30'), time_to_minutes('12:00')])
busy_intervals.append([time_to_minutes('12:30'), time_to_minutes('13:00')])
busy_intervals.append([time_to_minutes('13:30'), time_to_minutes('14:00')])
busy_intervals.append([time_to_minutes('14:30'), time_to_minutes('15:00')])
busy_intervals.append([time_to_minutes('15:30'), time_to_minutes('17:00')])

# Add busy intervals for Carolyn
busy_intervals.append([time_to_minutes('9:00'), time_to_minutes('10:30')])
busy_intervals.append([time_to_minutes('11:00'), time_to_minutes('11:30')])
busy_intervals.append([time_to_minutes('12:00'), time_to_minutes('13:00')])
busy_intervals.append([time_to_minutes('13:30'), time_to_minutes('14:30')])
busy_intervals.append([time_to_minutes('15:00'), time_to_minutes('17:00')])

# Add busy intervals for Kyle
busy_intervals.append([time_to_minutes('9:00'), time_to_minutes('9:30')])
busy_intervals.append([time_to_minutes('11:30'), time_to_minutes('12:00')])
busy_intervals.append([time_to_minutes('12:30'), time_to_minutes('13:00')])
busy_intervals.append([time_to_minutes('14:30'), time_to_minutes('17:00')])

# Clip intervals to work hours and filter out empty intervals
clipped_busy = []
for interval in busy_intervals:
    start, end = interval
    start = max(start, work_start)
    end = min(end, work_end)
    if start < end:
        clipped_busy.append([start, end])

# Merge overlapping or adjacent busy intervals
if not clipped_busy:
    merged_busy = []
else:
    clipped_busy.sort(key=lambda x: x[0])
    merged_busy = []
    start_curr, end_curr = clipped_busy[0]
    for i in range(1, len(clipped_busy)):
        s, e = clipped_busy[i]
        if s <= end_curr:
            end_curr = max(end_curr, e)
        else:
            merged_busy.append([start_curr, end_curr])
            start_curr, end_curr = s, e
    merged_busy.append([start_curr, end_curr])

# Compute free intervals
free_intervals = []
if not merged_busy:
    free_intervals.append([work_start, work_end])
else:
    # Before first busy interval
    if work_start < merged_busy[0][0]:
        free_intervals.append([work_start, merged_busy[0][0]])
    # Between busy intervals
    for i in range(len(merged_busy) - 1):
        gap_start = merged_busy[i][1]
        gap_end = merged_busy[i+1][0]
        if gap_start < gap_end:
            free_intervals.append([gap_start, gap_end])
    # After last busy interval
    if merged_busy[-1][1] < work_end:
        free_intervals.append([merged_busy[-1][1], work_end])

# Find the first free interval of sufficient duration
meeting_start = None
for interval in free_intervals:
    start, end = interval
    if end - start >= meeting_duration:
        meeting_start = start
        break

if meeting_start is not None:
    meeting_end = meeting_start + meeting_duration
    start_time_str = minutes_to_time_str(meeting_start)
    end_time_str = minutes_to_time_str(meeting_end)
    time_range_str = f"{start_time_str}:{end_time_str}"
    print("Monday")
    print(time_range_str)
else:
    print("No suitable time found")