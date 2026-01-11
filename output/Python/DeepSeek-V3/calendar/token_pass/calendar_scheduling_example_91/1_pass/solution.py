def time_to_minutes(t):
    """Convert 'HH:MM' to minutes from 9:00."""
    h, m = map(int, t.split(':'))
    return (h - 9) * 60 + m

def minutes_to_time(m):
    """Convert minutes from 9:00 to 'HH:MM'."""
    h = 9 + m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def merge_intervals(intervals):
    """Merge overlapping intervals."""
    if not intervals:
        return []
    intervals.sort(key=lambda x: x[0])
    merged = [intervals[0]]
    for start, end in intervals[1:]:
        last_start, last_end = merged[-1]
        if start <= last_end:
            merged[-1] = (last_start, max(last_end, end))
        else:
            merged.append((start, end))
    return merged

def find_free_slots(busy, day_start_min, day_end_min):
    """Find free slots given busy intervals."""
    free = []
    last_end = day_start_min
    for start, end in sorted(busy):
        if start > last_end:
            free.append((last_end, start))
        last_end = max(last_end, end)
    if last_end < day_end_min:
        free.append((last_end, day_end_min))
    return free

def intersect_slots(slots1, slots2):
    """Intersect two lists of free slots."""
    result = []
    i = j = 0
    while i < len(slots1) and j < len(slots2):
        start1, end1 = slots1[i]
        start2, end2 = slots2[j]
        start_max = max(start1, start2)
        end_min = min(end1, end2)
        if start_max < end_min:
            result.append((start_max, end_min))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return result

def main():
    # Work hours
    work_start = "9:00"
    work_end = "17:00"
    day_start_min = time_to_minutes(work_start)  # 0
    day_end_min = time_to_minutes(work_end)      # 480
    
    # Busy times in HH:MM format
    danielle_busy = [
        ("9:00", "10:00"),
        ("10:30", "11:00"),
        ("14:30", "15:00"),
        ("15:30", "16:00"),
        ("16:30", "17:00")
    ]
    bruce_busy = [
        ("11:00", "11:30"),
        ("12:30", "13:00"),
        ("14:00", "14:30"),
        ("15:30", "16:00")
    ]
    eric_busy = [
        ("9:00", "9:30"),
        ("10:00", "11:00"),
        ("11:30", "13:00"),
        ("14:30", "15:30")
    ]
    
    # Convert to minutes from 9:00
    def convert_list(lst):
        return [(time_to_minutes(s), time_to_minutes(e)) for s, e in lst]
    
    d_busy = merge_intervals(convert_list(danielle_busy))
    b_busy = merge_intervals(convert_list(bruce_busy))
    e_busy = merge_intervals(convert_list(eric_busy))
    
    # Find free slots for each
    d_free = find_free_slots(d_busy, day_start_min, day_end_min)
    b_free = find_free_slots(b_busy, day_start_min, day_end_min)
    e_free = find_free_slots(e_busy, day_start_min, day_end_min)
    
    # Intersect all
    common_free = intersect_slots(d_free, b_free)
    common_free = intersect_slots(common_free, e_free)
    
    # Meeting duration in minutes
    meeting_duration = 60
    
    # Find first slot that fits
    meeting_slot = None
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_slot = (start, start + meeting_duration)
            break
    
    # Output
    day_of_week = "Monday"
    if meeting_slot:
        start_time = minutes_to_time(meeting_slot[0])
        end_time = minutes_to_time(meeting_slot[1])
        print(f"{day_of_week} {start_time}:{end_time}")
    else:
        print("No suitable slot found")

if __name__ == "__main__":
    main()