def time_to_minutes(t):
    """Convert 'HH:MM' to minutes since midnight."""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes since midnight to 'HH:MM'."""
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def find_meeting_slot(work_start, work_end, duration, busy_a, busy_b):
    """
    work_start, work_end: 'HH:MM'
    duration: minutes
    busy_a, busy_b: list of tuples ('HH:MM', 'HH:MM')
    """
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    
    # Convert busy times to minutes
    busy_min_a = [(time_to_minutes(s), time_to_minutes(e)) for s, e in busy_a]
    busy_min_b = [(time_to_minutes(s), time_to_minutes(e)) for s, e in busy_b]
    
    # Merge and sort busy intervals for each person
    def merge_intervals(intervals):
        if not intervals:
            return []
        intervals.sort()
        merged = []
        current_start, current_end = intervals[0]
        for s, e in intervals[1:]:
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged.append((current_start, current_end))
                current_start, current_end = s, e
        merged.append((current_start, current_end))
        return merged
    
    merged_a = merge_intervals(busy_min_a)
    merged_b = merge_intervals(busy_min_b)
    
    # Find free slots for each person within work hours
    def free_slots(busy_intervals, start_bound, end_bound):
        free = []
        prev_end = start_bound
        for bs, be in busy_intervals:
            if bs > prev_end:
                free.append((prev_end, bs))
            prev_end = max(prev_end, be)
        if prev_end < end_bound:
            free.append((prev_end, end_bound))
        return free
    
    free_a = free_slots(merged_a, work_start_min, work_end_min)
    free_b = free_slots(merged_b, work_start_min, work_end_min)
    
    # Intersect free slots
    i, j = 0, 0
    possible_slots = []
    while i < len(free_a) and j < len(free_b):
        start = max(free_a[i][0], free_b[j][0])
        end = min(free_a[i][1], free_b[j][1])
        if start < end:
            possible_slots.append((start, end))
        if free_a[i][1] < free_b[j][1]:
            i += 1
        else:
            j += 1
    
    # Find slots with enough duration
    for start, end in possible_slots:
        if end - start >= duration:
            return minutes_to_time(start), minutes_to_time(start + duration)
    
    return None, None

# Define the problem
work_start = "09:00"
work_end = "17:00"
duration = 60  # minutes

james_busy = [("11:30", "12:00"), ("14:30", "15:00")]
john_busy = [("09:30", "11:00"), ("11:30", "12:00"), ("12:30", "13:30"), ("14:30", "16:30")]

start_time, end_time = find_meeting_slot(work_start, work_end, duration, james_busy, john_busy)

if start_time and end_time:
    print(f"Monday {{{start_time}:{end_time}}}")
else:
    print("No suitable slot found.")