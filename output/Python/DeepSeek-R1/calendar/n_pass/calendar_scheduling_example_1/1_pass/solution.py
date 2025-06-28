def invert_intervals(busy_intervals, start, end):
    if not busy_intervals:
        return [(start, end)]
    busy_intervals.sort(key=lambda x: x[0])
    free = []
    current = start
    for interval in busy_intervals:
        if current < interval[0]:
            free.append((current, interval[0]))
        current = max(current, interval[1])
    if current < end:
        free.append((current, end))
    return free

def intersect_intervals(intervals1, intervals2):
    if not intervals1 or not intervals2:
        return []
    i = j = 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        low = max(start1, start2)
        high = min(end1, end2)
        if low < high:
            result.append((low, high))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return result

def main():
    # Work day: 9:00 to 17:00 represented in minutes from 9:00 (0 minutes = 9:00, 480 minutes = 17:00)
    work_start = 0
    work_end = 480
    meeting_duration = 30
    # Billy's preference: avoid meetings after 15:00 (360 minutes from 9:00), so meeting must end by 360 (15:00) if possible
    billy_cutoff = 360
    
    # Busy intervals for each participant (each interval is (start_minute, end_minute), end exclusive)
    raymond_busy = [(0, 30), (150, 180), (240, 270), (360, 390)]
    billy_busy = [(60, 90), (180, 240), (450, 480)]
    donald_busy = [(0, 30), (60, 120), (180, 240), (300, 330), (420, 480)]
    
    # Calculate free intervals for each
    raymond_free = invert_intervals(raymond_busy, work_start, work_end)
    billy_free = invert_intervals(billy_busy, work_start, work_end)
    donald_free = invert_intervals(donald_busy, work_start, work_end)
    
    # Find common free intervals
    common_free = intersect_intervals(raymond_free, billy_free)
    common_free = intersect_intervals(common_free, donald_free)
    
    candidate_start = None
    # First, try to find a slot that ends by 15:00 (360 minutes)
    for start, end in common_free:
        slot_end = start + meeting_duration
        if slot_end > end:  # Not enough time in this interval
            continue
        if slot_end <= billy_cutoff:  # Ends by 15:00
            candidate_start = start
            break
    
    # If no candidate found that ends by 15:00, take the first available slot of sufficient length
    if candidate_start is None:
        for start, end in common_free:
            if end - start >= meeting_duration:
                candidate_start = start
                break
    
    # Convert candidate_start to time string
    total_minutes_start = candidate_start
    hours_start = 9 + total_minutes_start // 60
    minutes_start = total_minutes_start % 60
    total_minutes_end = candidate_start + meeting_duration
    hours_end = 9 + total_minutes_end // 60
    minutes_end = total_minutes_end % 60
    
    time_str = f"{hours_start:02d}:{minutes_start:02d}:{hours_end:02d}:{minutes_end:02d}"
    print("Monday")
    print(time_str)

if __name__ == "__main__":
    main()