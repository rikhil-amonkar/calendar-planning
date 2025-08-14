def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

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

ronald_busy = []
stephen_busy = [(10*60, 10*60+30), (12*60, 12*60+30)]
brittany_busy = [(11*60, 11*60+30), (13*60+30, 14*60), (15*60+30, 16*60), (16*60+30, 17*60)]
dorothy_busy = [(9*60, 9*60+30), (10*60, 10*60+30), (11*60, 12*60+30), (13*60, 15*60), (15*60+30, 17*60)]
rebecca_busy = [(9*60+30, 10*60+30), (11*60, 11*60+30), (12*60, 12*60+30), (13*60, 17*60)]
jordan_busy = [(9*60, 9*60+30), (10*60, 11*60), (11*60+30, 12*60), (13*60, 15*60), (15*60+30, 16*60+30)]

all_busies = ronald_busy + stephen_busy + brittany_busy + dorothy_busy + rebecca_busy + jordan_busy

merged = merge_intervals(all_busies)

work_start = 9 * 60
work_end = 17 * 60

free_intervals = []
prev_end = work_start
for interval in merged:
    start, end = interval
    if start > prev_end:
        free_intervals.append((prev_end, start))
    prev_end = max(prev_end, end)
if prev_end < work_end:
    free_intervals.append((prev_end, work_end))

meeting_start = None
meeting_end = None
for interval in free_intervals:
    start, end = interval
    if end - start >= 30:
        meeting_start = start
        meeting_end = start + 30
        break

time_range = f"{to_time_str(meeting_start)}:{to_time_str(meeting_end)}"
day = "Monday"

print(f"{time_range} {day}")