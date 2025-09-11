work_start = 9 * 60
work_end = 17 * 60
meeting_duration = 30

# Busy times for each participant
denise_busy = [(12 * 60, 12 * 60 + 30), (15 * 60 + 30, 16 * 60)]
natalie_busy = [(9 * 60, 11 * 60 + 30), (12 * 60, 13 * 60), (14 * 60, 14 * 60 + 30), (15 * 60, 17 * 60)]
angela_busy = []

all_busies = denise_busy + natalie_busy + angela_busy

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

merged = merge_intervals(all_busies)

free_intervals = []
prev_end = work_start
for interval in merged:
    start, end = interval
    if start > prev_end:
        free_intervals.append((prev_end, start))
    prev_end = end
if prev_end < work_end:
    free_intervals.append((prev_end, work_end))

def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours:02d}:{mins:02d}"

for free_start, free_end in free_intervals:
    if free_end - free_start >= meeting_duration:
        start_time = free_start
        end_time = start_time + meeting_duration
        start_str = minutes_to_time(start_time)
        end_str = minutes_to_time(end_time)
        day = "Monday"
        print(f"{{{start_str}:{end_str}}} {day}")
        break