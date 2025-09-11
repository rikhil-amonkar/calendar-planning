def adjust_to_time_frame(busy_intervals, start_time, end_time):
    adjusted = []
    for interval in busy_intervals:
        start_h, start_m, end_h, end_m = interval
        start_min = start_h * 60 + start_m
        end_min = end_h * 60 + end_m
        tf_start = start_time
        tf_end = end_time
        new_start = max(start_min, tf_start)
        new_end = min(end_min, tf_end)
        if new_start < new_end:
            adjusted.append( 
                (new_start // 60, new_start % 60, new_end // 60, new_end % 60) 
            )
    return adjusted

def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0]*60 + x[1])
    merged = [sorted_intervals[0]]
    for current in sorted_intervals[1:]:
        last = merged[-1]
        last_start = last[0] * 60 + last[1]
        last_end = last[2] * 60 + last[3]
        current_start = current[0] * 60 + current[1]
        current_end = current[2] * 60 + current[3]
        if current_start <= last_end:
            new_start = last_start
            new_end = max(last_end, current_end)
            merged[-1] = (
                new_start // 60, new_start % 60,
                new_end // 60, new_end % 60
            )
        else:
            merged.append(current)
    return merged

def get_free_slots(busy_intervals, start_work, end_work):
    merged = merge_intervals(busy_intervals)
    free_slots = []
    current_time = start_work * 60  # convert to minutes
    for interval in merged:
        start_h, start_m, end_h, end_m = interval
        busy_start = start_h * 60 + start_m
        busy_end = end_h * 60 + end_m
        if busy_start > current_time:
            free_start = current_time
            free_end = busy_start
            duration = free_end - free_start
            if duration >= 30:  # Corrected from 30 * 60 to 30
                free_slots.append( (free_start // 60, free_start % 60, free_end // 60, free_end % 60) )
        current_time = max(current_time, busy_end)
    # Check after last busy interval
    if current_time < end_work * 60:
        free_start = current_time
        free_end = end_work * 60
        duration = free_end - free_start
        if duration >= 30:  # Corrected from 30 * 60 to 30
            free_slots.append( (free_start // 60, free_start % 60, free_end // 60, free_end % 60) )
    return free_slots

# Define busy times for Tuesday
amanda_tuesday = [
    (9, 0, 9, 30),
    (10, 0, 10, 30),
    (11, 30, 12, 0),
    (13, 30, 14, 30),
    (15, 30, 16, 0),
    (16, 30, 17, 0),
]
nathan_tuesday = [
    (9, 0, 10, 30),
    (11, 0, 13, 0),
    (13, 30, 14, 0),
    (14, 30, 15, 30),
    (16, 0, 16, 30),
]

# Time frame for Tuesday is 9:00 to 11:00
start_time = 9  # hours
end_time = 11   # hours

# Adjust busy intervals to the time frame
amanda_adjusted = adjust_to_time_frame(amanda_tuesday, start_time*60, end_time*60)
nathan_adjusted = adjust_to_time_frame(nathan_tuesday, start_time*60, end_time*60)

# Combine all busy intervals
combined_busies = amanda_adjusted + nathan_adjusted

# Merge them
merged_busies = merge_intervals(combined_busies)

# Generate free slots between 9:00 and 11:00
free_slots = get_free_slots(merged_busies, start_time, end_time)

# Output the first available slot
if free_slots:
    slot = free_slots[0]
    start_h, start_m, end_h, end_m = slot
    day = "Tuesday"
    print(f"{day}: {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")
else:
    print("No available time")