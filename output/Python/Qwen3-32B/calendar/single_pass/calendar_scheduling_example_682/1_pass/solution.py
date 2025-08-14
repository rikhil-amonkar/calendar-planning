def to_minutes(h, m):
    return h * 60 + m

def clip_intervals(intervals, window_start, window_end):
    clipped = []
    for start, end in intervals:
        if end <= window_start or start >= window_end:
            continue
        new_start = max(start, window_start)
        new_end = min(end, window_end)
        clipped.append((new_start, new_end))
    return clipped

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

def find_free_slots(merged, window_start, window_end):
    free_slots = []
    prev_end = window_start
    for interval in merged:
        start, end = interval
        if prev_end < start:
            free_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < window_end:
        free_slots.append((prev_end, window_end))
    return free_slots

def main():
    # Amanda's Tuesday busy times in minutes
    amanda_tue = [
        (to_minutes(9, 0), to_minutes(9, 30)),
        (to_minutes(10, 0), to_minutes(10, 30)),
        (to_minutes(11, 30), to_minutes(12, 0)),
        (to_minutes(13, 30), to_minutes(14, 30)),
        (to_minutes(15, 30), to_minutes(16, 0)),
        (to_minutes(16, 30), to_minutes(17, 0)),
    ]
    # Nathan's Tuesday busy times
    nathan_tue = [
        (to_minutes(9, 0), to_minutes(10, 30)),
        (to_minutes(11, 0), to_minutes(13, 0)),
        (to_minutes(13, 30), to_minutes(14, 0)),
        (to_minutes(14, 30), to_minutes(15, 30)),
        (to_minutes(16, 0), to_minutes(16, 30)),
        (to_minutes(16, 30), to_minutes(17, 0)),
    ]
    # Window for Amanda's constraint on Tuesday
    window_start = to_minutes(9, 0)
    window_end = to_minutes(11, 0)
    
    # Clip intervals to the window
    amanda_clipped = clip_intervals(amanda_tue, window_start, window_end)
    nathan_clipped = clip_intervals(nathan_tue, window_start, window_end)
    all_clipped = amanda_clipped + nathan_clipped
    
    # Merge intervals
    merged = merge_intervals(all_clipped)
    
    # Find free slots
    free_slots = find_free_slots(merged, window_start, window_end)
    
    # Find the first free slot with at least 30 minutes
    for start, end in free_slots:
        if end - start >= 30:
            start_time = f"{start//60:02d}:{start%60:02d}"
            end_time = f"{end//60:02d}:{end%60:02d}"
            print(f"{start_time}:{end_time} Tuesday")
            return
    
    # If no slot found (though problem says there is a solution)
    print("No suitable time found")

if __name__ == "__main__":
    main()