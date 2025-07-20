def parse_time(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

def compute_free_intervals(busy_intervals, work_start, work_end):
    if not busy_intervals:
        return [(work_start, work_end)]
    
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    merged = []
    current_start, current_end = sorted_busy[0]
    for interval in sorted_busy[1:]:
        if interval[0] <= current_end:
            current_end = max(current_end, interval[1])
        else:
            merged.append((current_start, current_end))
            current_start, current_end = interval
    merged.append((current_start, current_end))
    
    free_intervals = []
    if work_start < merged[0][0]:
        free_intervals.append((work_start, merged[0][0]))
    
    for i in range(len(merged) - 1):
        gap_start = merged[i][1]
        gap_end = merged[i+1][0]
        if gap_start < gap_end:
            free_intervals.append((gap_start, gap_end))
            
    if merged[-1][1] < work_end:
        free_intervals.append((merged[-1][1], work_end))
        
    return free_intervals

def intersect_intervals(intervals_a, intervals_b):
    i, j = 0, 0
    result = []
    while i < len(intervals_a) and j < len(intervals_b):
        a_start, a_end = intervals_a[i]
        b_start, b_end = intervals_b[j]
        start_max = max(a_start, b_start)
        end_min = min(a_end, b_end)
        if start_max < end_min:
            result.append((start_max, end_min))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return result

def main():
    work_start = 540  # 9:00
    work_end = 1020    # 17:00
    duration = 30
    
    bobby_busy = {
        "Monday": [("14:30", "15:00")],
        "Tuesday": [("9:00", "11:30"), ("12:00", "12:30"), ("13:00", "15:00"), ("15:30", "17:00")]
    }
    
    michael_busy = {
        "Monday": [("9:00", "10:00"), ("10:30", "13:30"), ("14:00", "15:00"), ("15:30", "17:00")],
        "Tuesday": [("9:00", "10:30"), ("11:00", "11:30"), ("12:00", "14:00"), ("15:00", "16:00"), ("16:30", "17:00")]
    }
    
    days = ["Monday", "Tuesday"]
    for day in days:
        bobby_list = [(parse_time(s), parse_time(e)) for s, e in bobby_busy[day]]
        michael_list = [(parse_time(s), parse_time(e)) for s, e in michael_busy[day]]
        
        bobby_free = compute_free_intervals(bobby_list, work_start, work_end)
        michael_free = compute_free_intervals(michael_list, work_start, work_end)
        
        common_free = intersect_intervals(bobby_free, michael_free)
        
        for start, end in common_free:
            if end - start >= duration:
                meeting_start = start
                meeting_end = meeting_start + duration
                start_str = minutes_to_time(meeting_start)
                end_str = minutes_to_time(meeting_end)
                print(day)
                print(f"{start_str}:{end_str}")
                return
                
    print("No suitable time found")

if __name__ == "__main__":
    main()