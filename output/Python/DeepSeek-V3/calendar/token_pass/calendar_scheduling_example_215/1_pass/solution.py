def time_to_minutes(t):
    """Convert HH:MM to minutes from 00:00"""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes from 00:00 to HH:MM"""
    return f"{m // 60:02d}:{m % 60:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    intervals.sort(key=lambda x: x[0])
    merged = [intervals[0]]
    for current in intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

def find_free_slot(busy_intervals, work_start, work_end, duration):
    # Convert busy to minutes from 00:00
    busy = [(time_to_minutes(s), time_to_minutes(e)) for s, e in busy_intervals]
    busy = merge_intervals(busy)
    
    # Work bounds in minutes
    start_min = time_to_minutes(work_start)
    end_min = time_to_minutes(work_end)
    
    # Find gaps
    prev_end = start_min
    for bs, be in busy:
        if bs > prev_end and bs - prev_end >= duration:
            return (prev_end, prev_end + duration)
        prev_end = max(prev_end, be)
    if end_min - prev_end >= duration:
        return (prev_end, prev_end + duration)
    return None

def main():
    # Work hours
    work_start = "09:00"
    work_end = "17:00"
    duration_minutes = 30
    
    # Busy times in HH:MM format
    busy_times = [
        # Cynthia
        ("09:30", "10:30"),
        ("11:30", "12:00"),
        ("13:00", "13:30"),
        ("15:00", "16:00"),
        # Lauren
        ("09:00", "09:30"),
        ("10:30", "11:00"),
        ("11:30", "12:00"),
        ("13:00", "13:30"),
        ("14:00", "14:30"),
        ("15:00", "15:30"),
        ("16:00", "17:00"),
        # Robert
        ("10:30", "11:00"),
        ("11:30", "12:00"),
        ("12:30", "13:30"),
        ("14:00", "16:00"),
    ]
    
    slot = find_free_slot(busy_times, work_start, work_end, duration_minutes)
    
    if slot:
        start_str = minutes_to_time(slot[0])
        end_str = minutes_to_time(slot[1])
        print(f"{start_str}:{end_str}")
        print("Monday")
    else:
        print("No slot found")

if __name__ == "__main__":
    main()