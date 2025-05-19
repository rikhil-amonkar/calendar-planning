def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = [list(sorted_intervals[0])]
    for current in sorted_intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1][1] = max(last[1], current[1])
        else:
            merged.append(list(current))
    return merged

def minutes_to_time(minutes):
    hours = 9 + minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define busy intervals in minutes since 9:00
michael_busy = [(30, 90), (360, 390), (420, 450)]
arthur_busy = [(0, 180), (240, 360), (390, 420), (450, 480)]
busy = michael_busy + arthur_busy

merged = merge_intervals(busy)

free_intervals = []
prev_end = 0
for start, end in merged:
    if start > prev_end:
        free_intervals.append((prev_end, start))
    prev_end = max(prev_end, end)
if prev_end < 480:
    free_intervals.append((prev_end, 480))

# Find the first suitable slot
meeting_duration = 30
proposed_slot = None
for slot in free_intervals:
    start, end = slot
    if end - start >= meeting_duration:
        proposed_slot = (start, start + meeting_duration)
        break

# Format the output
start_time = minutes_to_time(proposed_slot[0])
end_time = minutes_to_time(proposed_slot[1])
print(f"Monday {start_time}:{end_time}")