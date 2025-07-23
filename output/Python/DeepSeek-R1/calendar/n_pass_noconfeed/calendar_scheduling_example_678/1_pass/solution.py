def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return hours * 60 + minutes

def minutes_to_time(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = []
    start, end = sorted_intervals[0]
    for i in range(1, len(sorted_intervals)):
        s, e = sorted_intervals[i]
        if s <= end:
            if e > end:
                end = e
        else:
            merged.append((start, end))
            start, end = s, e
    merged.append((start, end))
    return merged

def compute_free_intervals(busy_intervals, work_start, work_end):
    if not busy_intervals:
        return [(work_start, work_end)]
    merged_busy = merge_intervals(busy_intervals)
    free = []
    current = work_start
    for start_busy, end_busy in merged_busy:
        if current < start_busy:
            free.append((current, start_busy))
        current = max(current, end_busy)
    if current < work_end:
        free.append((current, work_end))
    return free

def find_common_intervals(free1, free2):
    common = []
    for a_start, a_end in free1:
        for b_start, b_end in free2:
            start_common = max(a_start, b_start)
            end_common = min(a_end, b_end)
            if start_common < end_common:
                common.append((start_common, end_common))
    return common

def main():
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    russell_busy = {
        'Monday': [(time_to_minutes("10:30"), time_to_minutes("11:00"))],
        'Tuesday': [(time_to_minutes("13:00"), time_to_minutes("13:30"))]
    }
    alexander_busy = {
        'Monday': [
            (time_to_minutes("9:00"), time_to_minutes("11:30")),
            (time_to_minutes("12:00"), time_to_minutes("14:30")),
            (time_to_minutes("15:00"), time_to_minutes("17:00"))
        ],
        'Tuesday': [
            (time_to_minutes("9:00"), time_to_minutes("10:00")),
            (time_to_minutes("13:00"), time_to_minutes("14:00")),
            (time_to_minutes("15:00"), time_to_minutes("15:30")),
            (time_to_minutes("16:00"), time_to_minutes("16:30"))
        ]
    }
    preference_threshold = time_to_minutes("13:30")  # 13:30 in minutes

    days = ['Monday', 'Tuesday']
    candidates = []

    for day in days:
        russell_busy_today = russell_busy.get(day, [])
        alexander_busy_today = alexander_busy.get(day, [])
        
        russell_free = compute_free_intervals(russell_busy_today, work_start, work_end)
        alexander_free = compute_free_intervals(alexander_busy_today, work_start, work_end)
        
        common_free = find_common_intervals(russell_free, alexander_free)
        
        for interval in common_free:
            start_int, end_int = interval
            duration = end_int - start_int
            if duration < 60:
                continue
            if day == 'Monday':
                meeting_start = start_int
                meeting_end = meeting_start + 60
                candidates.append((0, day, meeting_start, meeting_end))
            else:
                candidate_start1 = max(start_int, preference_threshold)
                if candidate_start1 + 60 <= end_int:
                    candidates.append((1, day, candidate_start1, candidate_start1 + 60))
                if start_int < preference_threshold:
                    meeting_end = start_int + 60
                    if meeting_end <= end_int and meeting_end <= preference_threshold:
                        candidates.append((2, day, start_int, meeting_end))
    
    if not candidates:
        print("No suitable time found.")
        return
    
    candidates_sorted = sorted(candidates, key=lambda x: (x[0], x[2]))
    best = candidates_sorted[0]
    day_str = best[1]
    start_time_str = minutes_to_time(best[2])
    end_time_str = minutes_to_time(best[3])
    time_range_str = f"{start_time_str}:{end_time_str}"
    print(day_str)
    print(time_range_str)

if __name__ == "__main__":
    main()