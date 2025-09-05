def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(busy, work_start, work_end):
    free = []
    current = work_start
    for start, end in sorted(busy):
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    intersections = []
    for s1, e1 in intervals1:
        for s2, e2 in intervals2:
            start = max(s1, s2)
            end = min(e1, e2)
            if start < end:
                intersections.append((start, end))
    return intersections

def main():
    meeting_duration = 30  # duration in minutes
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    
    # Lisa's busy times on Monday
    lisa_busy = [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("14:00"), time_to_minutes("16:00"))
    ]
    
    # Anthony's busy times on Monday
    anthony_busy = [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:30"), time_to_minutes("13:30")),
        (time_to_minutes("14:00"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
    
    lisa_free = get_free_intervals(lisa_busy, work_start, work_end)
    anthony_free = get_free_intervals(anthony_busy, work_start, work_end)
    
    common_free = intersect_intervals(lisa_free, anthony_free)
    
    # Find earliest slot with at least the meeting duration
    slot = None
    for start, end in sorted(common_free):
        if end - start >= meeting_duration:
            slot = (start, start + meeting_duration)
            break
            
    if slot:
        meeting_time = f"{minutes_to_time(slot[0])}:{minutes_to_time(slot[1])}"
        meeting_day = "Monday"
        print(meeting_time)
        print(meeting_day)
    else:
        print("No available slot found.")

if __name__ == "__main__":
    main()