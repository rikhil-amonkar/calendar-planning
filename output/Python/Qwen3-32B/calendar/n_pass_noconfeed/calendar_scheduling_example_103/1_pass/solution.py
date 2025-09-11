def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = [sorted(intervals)[0]]
    for current in sorted_intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1] = [last[0], max(last[1], current[1])]
        else:
            merged.append(current)
    return merged

def find_free_slot(work_start, work_end, blocked):
    merged_blocked = merge_intervals(blocked)
    free_intervals = []
    prev_end = work_start
    for interval in merged_blocked:
        start, end = interval
        if start > prev_end:
            free_intervals.append([prev_end, start])
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free_intervals.append([prev_end, work_end])
    # Check for a 30-minute slot
    for interval in free_intervals:
        start, end = interval
        duration = end - start
        if duration >= 30:
            # Return the first possible 30-minute slot
            return (start, start + 30)
    return None  # No slot found, but problem says there is one

# Define work hours in minutes
work_start = 9 * 60
work_end = 17 * 60

# Blocked intervals for all participants
blocked_intervals = [
    [570, 600], [870, 900],  # Diane
    [810, 840], [870, 900],  # Jack
    [540, 600], [630, 690], [720, 870], [900, 990],  # Eugene
    [570, 630], [660, 720], [750, 840], [900, 990]  # Patricia
]

# Find the free slot
free_slot = find_free_slot(work_start, work_end, blocked_intervals)
start_time, end_time = free_slot

# Convert to time strings
start_str = minutes_to_time(start_time)
end_str = minutes_to_time(end_time)

# Output
print(f"{start_str}:{end_str} Monday")