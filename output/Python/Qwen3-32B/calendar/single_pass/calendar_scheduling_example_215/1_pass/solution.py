def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = [list(sorted_intervals[0])]
    for current in sorted_intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            # Overlapping or adjacent, merge them
            if current[1] > last[1]:
                last[1] = current[1]
        else:
            merged.append(list(current))
    # Convert back to tuples
    return [tuple(interval) for interval in merged]

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Work hours in minutes
work_start = 9 * 60
work_end = 17 * 60

# Busy intervals for each person
busy_cynthia = [
    (9*60 + 30, 10*60 + 30),  # 9:30-10:30
    (11*60 + 30, 12*60),     # 11:30-12:00
    (13*60, 13*60 + 30),     # 13:00-13:30
    (15*60, 16*60)           # 15:00-16:00
]

busy_lauren = [
    (9*60, 9*60 + 30),        # 9:00-9:30
    (10*60 + 30, 11*60),     # 10:30-11:00
    (11*60 + 30, 12*60),     # 11:30-12:00
    (13*60, 13*60 + 30),     # 13:00-13:30
    (14*60, 14*60 + 30),     # 14:00-14:30
    (15*60, 15*60 + 30),     # 15:00-15:30
    (16*60, 17*60)           # 16:00-17:00
]

busy_robert = [
    (10*60 + 30, 11*60),     # 10:30-11:00
    (11*60 + 30, 12*60),     # 11:30-12:00
    (12*60 + 30, 13*60 + 30),# 12:30-13:30
    (14*60, 16*60)           # 14:00-16:00
]

# Combine all busy intervals
all_busy = busy_cynthia + busy_lauren + busy_robert

# Merge intervals
merged = merge_intervals(all_busy)

# Find free slots
free_slots = []
prev_end = work_start
for interval in merged:
    start, end = interval
    if start > prev_end:
        free_slots.append( (prev_end, start) )
    prev_end = max(prev_end, end)
# Check after last interval
if prev_end < work_end:
    free_slots.append( (prev_end, work_end) )

# Find the earliest slot with at least 30 minutes
meeting_duration = 30
for slot in free_slots:
    start, end = slot
    if end - start >= meeting_duration:
        # The earliest one is the first valid
        start_time = to_time_str(start)
        end_time = to_time_str(start + meeting_duration)
        day = "Monday"
        print(f"{start_time}:{end_time} {day}")
        break