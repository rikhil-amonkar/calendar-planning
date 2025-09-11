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

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

adam_busy = [(14*60, 15*60)]
john_busy = [(13*60, 13*60+30), (14*60, 14*60+30), (15*60+30, 16*60), (16*60+30, 17*60)]
stephanie_busy = [(9*60+30, 10*60), (10*60+30, 11*60), (11*60+30, 16*60), (16*60+30, 17*60)]
anna_busy = [(9*60+30, 10*60), (12*60, 12*60+30), (13*60, 15*60+30), (16*60+30, 17*60)]

all_buses = adam_busy + john_busy + stephanie_busy + anna_busy

merged = merge_intervals(all_buses)

free_intervals = []
prev_end = 9 * 60  # Start of work day
for interval in merged:
    start, end = interval
    if prev_end < start:
        free_intervals.append((prev_end, start))
    prev_end = end

# Add the end of the day
if prev_end < 17 * 60:
    free_intervals.append((prev_end, 17 * 60))

# Find suitable time
for interval in free_intervals:
    start, end = interval
    duration = end - start
    if duration >= 30:
        # Check Anna's preference: meeting starts at or after 14:30 (870)
        required_start = max(start, 14 * 60 + 30)  # 870
        if required_start + 30 <= end:
            meeting_start = required_start
            meeting_end = meeting_start + 30
            start_str = to_time_str(meeting_start)
            end_str = to_time_str(meeting_end)
            print(f"{start_str}:{end_str} Monday")
            break