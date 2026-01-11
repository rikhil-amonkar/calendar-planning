def time_to_minutes(t):
    """Convert HH:MM to minutes from 00:00."""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes from 00:00 to HH:MM."""
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Work hours
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    
    # Bobby's preference: end by 15:00
    latest_end = time_to_minutes("15:00")
    
    # Meeting duration in minutes
    duration = 30
    
    # Busy intervals in minutes from 00:00
    lisa_busy = [
        ("09:00", "10:00"),
        ("10:30", "11:30"),
        ("12:30", "13:00"),
        ("16:00", "16:30"),
    ]
    bobby_busy = [
        ("09:00", "09:30"),
        ("10:00", "10:30"),
        ("11:30", "12:00"),
        ("15:00", "15:30"),
    ]
    randy_busy = [
        ("09:30", "10:00"),
        ("10:30", "11:00"),
        ("11:30", "12:30"),
        ("13:00", "13:30"),
        ("14:30", "15:30"),
        ("16:00", "16:30"),
    ]
    
    def convert_intervals(intervals):
        return [(time_to_minutes(s), time_to_minutes(e)) for s, e in intervals]
    
    lisa_busy_min = convert_intervals(lisa_busy)
    bobby_busy_min = convert_intervals(bobby_busy)
    randy_busy_min = convert_intervals(randy_busy)
    
    # Generate free intervals for each person within work hours
    def free_intervals(busy, start_limit, end_limit):
        busy = sorted(busy, key=lambda x: x[0])
        free = []
        current = start_limit
        for s, e in busy:
            if s > current:
                free.append((current, s))
            current = max(current, e)
        if current < end_limit:
            free.append((current, end_limit))
        # Filter out zero-length intervals
        free = [(s, e) for s, e in free if e - s > 0]
        return free
    
    lisa_free = free_intervals(lisa_busy_min, work_start, work_end)
    bobby_free = free_intervals(bobby_busy_min, work_start, work_end)
    randy_free = free_intervals(randy_busy_min, work_start, work_end)
    
    # Find common free slots of at least `duration` minutes, ending by latest_end
    candidates = []
    for ls, le in lisa_free:
        for bs, be in bobby_free:
            # Intersect
            s = max(ls, bs)
            e = min(le, be)
            if e - s >= duration:
                for rs, re in randy_free:
                    s2 = max(s, rs)
                    e2 = min(e, re)
                    if e2 - s2 >= duration:
                        # This is a common free interval, now split into possible start times
                        start = s2
                        while start + duration <= e2:
                            end = start + duration
                            if end <= latest_end:  # Bobby's preference
                                candidates.append((start, end))
                            start += 1  # check every minute for earliest
    
    if not candidates:
        print("No suitable slot found")
        return
    
    # Choose earliest start time
    candidates.sort(key=lambda x: x[0])
    best_start, best_end = candidates[0]
    
    print(f"Monday {minutes_to_time(best_start)}:{minutes_to_time(best_end)}")

if __name__ == "__main__":
    main()