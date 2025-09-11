def adjust_busy_times(busy_intervals, work_start, meeting_end):
    adjusted = []
    for start, end in busy_intervals:
        new_start = max(start, work_start)
        new_end = min(end, meeting_end)
        if new_start < new_end:
            adjusted.append((new_start, new_end))
    return adjusted

def get_available_intervals(busy_intervals, work_start, work_end):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    available = []
    prev_end = work_start
    for start, end in sorted_busy:
        if prev_end < start:
            available.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        available.append((prev_end, work_end))
    return available

def find_overlaps(intervals1, intervals2):
    overlaps = []
    for a_start, a_end in intervals1:
        for b_start, b_end in intervals2:
            start = max(a_start, b_start)
            end = min(a_end, b_end)
            if start < end:
                overlaps.append((start, end))
    return overlaps

def to_time_str(hour_float):
    hour = int(hour_float)
    minute = int((hour_float - hour) * 60)
    return f"{hour:02d}:{minute:02d}"

# Define participants' busy times
christine_busy = [(11.0, 11.5), (15.0, 15.5)]
helen_busy = [(9.5, 10.5), (11.0, 11.5), (12.0, 12.5), (13.5, 16.0), (16.5, 17.0)]

work_start = 9.0
meeting_end = 15.0  # Helen can't meet after 15:00

# Adjust busy times for both
adjusted_christine = adjust_busy_times(christine_busy, work_start, meeting_end)
adjusted_helen = adjust_busy_times(helen_busy, work_start, meeting_end)

# Get available intervals
available_christine = get_available_intervals(adjusted_christine, work_start, meeting_end)
available_helen = get_available_intervals(adjusted_helen, work_start, meeting_end)

# Find overlaps
overlaps = find_overlaps(available_christine, available_helen)

# Filter for at least 30 minutes (0.5 hours)
meeting_duration = 0.5
suitable_slots = [slot for slot in overlaps if (slot[1] - slot[0]) >= meeting_duration]

# Find the earliest slot
earliest = min(suitable_slots, key=lambda x: x[0])

# Format output
start_str = to_time_str(earliest[0])
end_str = to_time_str(earliest[1])
day = "Monday"
print(f"{start_str}:{end_str} {day}")