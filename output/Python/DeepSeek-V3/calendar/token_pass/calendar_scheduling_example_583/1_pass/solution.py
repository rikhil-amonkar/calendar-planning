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
    
    # Busy intervals in minutes from 00:00
    lisa_busy = [
        ("09:00", "09:30"),
        ("10:30", "11:00"),
        ("14:00", "16:00"),
    ]
    anthony_busy = [
        ("09:00", "09:30"),
        ("11:00", "11:30"),
        ("12:30", "13:30"),
        ("14:00", "15:00"),
        ("15:30", "16:00"),
        ("16:30", "17:00"),
    ]
    
    # Convert to minutes since midnight
    def convert_intervals(intervals):
        return [(time_to_minutes(s), time_to_minutes(e)) for s, e in intervals]
    
    lisa_busy_min = convert_intervals(lisa_busy)
    anthony_busy_min = convert_intervals(anthony_busy)
    
    # Merge and sort busy intervals for each person
    def merge_intervals(intervals):
        if not intervals:
            return []
        sorted_intervals = sorted(intervals, key=lambda x: x[0])
        merged = []
        current = sorted_intervals[0]
        for start, end in sorted_intervals[1:]:
            if start <= current[1]:
                current = (current[0], max(current[1], end))
            else:
                merged.append(current)
                current = (start, end)
        merged.append(current)
        return merged
    
    lisa_merged = merge_intervals(lisa_busy_min)
    anthony_merged = merge_intervals(anthony_busy_min)
    
    # Combine busy times: a time is busy if either is busy
    all_busy = []
    i, j = 0, 0
    while i < len(lisa_merged) and j < len(anthony_merged):
        s1, e1 = lisa_merged[i]
        s2, e2 = anthony_merged[j]
        start = min(s1, s2)
        if s1 < e2 and s2 < e1:  # overlap
            end = max(e1, e2)
            all_busy.append((start, end))
            i += 1
            j += 1
        elif s1 < s2:
            all_busy.append((s1, e1))
            i += 1
        else:
            all_busy.append((s2, e2))
            j += 1
    while i < len(lisa_merged):
        all_busy.append(lisa_merged[i])
        i += 1
    while j < len(anthony_merged):
        all_busy.append(anthony_merged[j])
        j += 1
    
    # Merge again to combine overlapping/adjacent intervals
    all_busy = merge_intervals(all_busy)
    
    # Find earliest free slot of 30 minutes within work hours
    duration = 30
    current_time = work_start
    
    for start_busy, end_busy in all_busy:
        if current_time + duration <= start_busy:
            # Slot found
            meeting_start = current_time
            meeting_end = meeting_start + duration
            print(f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}")
            print("Monday")
            return
        # Move current_time to after this busy period if it's later
        if end_busy > current_time:
            current_time = end_busy
    
    # Check after last busy period
    if current_time + duration <= work_end:
        meeting_start = current_time
        meeting_end = meeting_start + duration
        print(f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}")
        print("Monday")
        return
    
    print("No slot found")

if __name__ == "__main__":
    main()