def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    if not busy_intervals:
        return [(work_start, work_end)]
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current_start = work_start
    for start, end in sorted_busy:
        if current_start < start:
            free.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < work_end:
        free.append((current_start, work_end))
    return free

def intersect_intervals(intervals_a, intervals_b):
    i, j = 0, 0
    common = []
    while i < len(intervals_a) and j < len(intervals_b):
        a_start, a_end = intervals_a[i]
        b_start, b_end = intervals_b[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            common.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return common

def main():
    work_start_min = time_to_minutes("9:00")
    work_end_min = time_to_minutes("17:00")
    meeting_duration = 30

    amy_busy = {
        'Wednesday': [
            (time_to_minutes("11:00"), time_to_minutes("11:30")),
            (time_to_minutes("13:30"), time_to_minutes("14:00"))
        ]
    }

    pamela_busy = {
        'Wednesday': [
            (time_to_minutes("9:00"), time_to_minutes("9:30")),
            (time_to_minutes("10:00"), time_to_minutes("11:00")),
            (time_to_minutes("11:30"), time_to_minutes("13:30")),
            (time_to_minutes("14:30"), time_to_minutes("15:00")),
            (time_to_minutes("16:00"), time_to_minutes("16:30"))
        ]
    }

    # Only consider Wednesday due to preference
    day = "Wednesday"
    
    # Get free intervals for Amy and Pamela on Wednesday
    amy_free = get_free_intervals(amy_busy.get(day, []), work_start_min, work_end_min)
    pamela_free = get_free_intervals(pamela_busy[day], work_start_min, work_end_min)
    
    # Find common free intervals
    common_free = intersect_intervals(amy_free, pamela_free)
    
    # Filter for intervals starting at or after 16:00 (960 minutes)
    preferred_start_min = time_to_minutes("16:00")
    candidate = None
    for start, end in common_free:
        if start >= preferred_start_min and (end - start) >= meeting_duration:
            candidate = (start, start + meeting_duration)
            break
    
    if candidate:
        start_min, end_min = candidate
        start_time = minutes_to_time(start_min)
        end_time = minutes_to_time(end_min)
        print(day)
        print(f"{start_time}:{end_time}")

if __name__ == "__main__":
    main()