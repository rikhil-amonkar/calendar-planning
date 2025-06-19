def time_str_to_minutes(time_str):
    h, m = time_str.split(':')
    return (int(h) - 9) * 60 + int(m)

def get_free_intervals(busy_intervals, start, end):
    if not busy_intervals:
        return [(start, end)]
    intervals_in_range = []
    for s, e in busy_intervals:
        low = max(s, start)
        high = min(e, end)
        if low < high:
            intervals_in_range.append((low, high))
    if not intervals_in_range:
        return [(start, end)]
    intervals_in_range.sort(key=lambda x: x[0])
    free = []
    current = start
    for s, e in intervals_in_range:
        if current < s:
            free.append((current, s))
        current = e
    if current < end:
        free.append((current, end))
    return free

def intersect_intervals(intervals1, intervals2):
    i = j = 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        a1, a2 = intervals1[i]
        b1, b2 = intervals2[j]
        low = max(a1, b1)
        high = min(a2, b2)
        if low < high:
            result.append((low, high))
        if a2 < b2:
            i += 1
        else:
            j += 1
    return result

def main():
    work_start = 0
    work_end = 480  # 9:00 to 17:00 is 8 hours = 480 minutes
    
    # Define busy intervals in minutes (relative to 9:00)
    natalie_busy = []
    david_busy = [(time_str_to_minutes("11:30"), time_str_to_minutes("12:00")), 
                  (time_str_to_minutes("14:30"), time_str_to_minutes("15:00"))]
    douglas_busy = [(time_str_to_minutes("9:30"), time_str_to_minutes("10:00")),
                    (time_str_to_minutes("11:30"), time_str_to_minutes("12:00")),
                    (time_str_to_minutes("13:00"), time_str_to_minutes("13:30")),
                    (time_str_to_minutes("14:30"), time_str_to_minutes("15:00"))]
    ralph_busy = [(time_str_to_minutes("9:00"), time_str_to_minutes("9:30")),
                  (time_str_to_minutes("10:00"), time_str_to_minutes("11:00")),
                  (time_str_to_minutes("11:30"), time_str_to_minutes("12:30")),
                  (time_str_to_minutes("13:30"), time_str_to_minutes("15:00")),
                  (time_str_to_minutes("15:30"), time_str_to_minutes("16:00")),
                  (time_str_to_minutes("16:30"), time_str_to_minutes("17:00"))]
    jordan_busy = [(time_str_to_minutes("9:00"), time_str_to_minutes("10:00")),
                   (time_str_to_minutes("12:00"), time_str_to_minutes("12:30")),
                   (time_str_to_minutes("13:00"), time_str_to_minutes("13:30")),
                   (time_str_to_minutes("14:30"), time_str_to_minutes("15:00")),
                   (time_str_to_minutes("15:30"), time_str_to_minutes("17:00"))]
    
    # David's constraint: only available after 14:00 (300 minutes)
    david_constraint_start = time_str_to_minutes("14:00")
    
    # Get free intervals for each participant
    natalie_free = get_free_intervals(natalie_busy, work_start, work_end)
    david_free = get_free_intervals(david_busy, david_constraint_start, work_end)
    douglas_free = get_free_intervals(douglas_busy, work_start, work_end)
    ralph_free = get_free_intervals(ralph_busy, work_start, work_end)
    jordan_free = get_free_intervals(jordan_busy, work_start, work_end)
    
    # Compute common free intervals
    common_free = natalie_free
    for free_intervals in [david_free, douglas_free, ralph_free, jordan_free]:
        common_free = intersect_intervals(common_free, free_intervals)
    
    # Find the first 30-minute slot
    meeting_duration = 30
    meeting_start = None
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_start = start
            break
    
    if meeting_start is None:
        # According to the problem, there is a solution, so this should not happen.
        print("Monday")
        print("00:00:00:00")
        return
    
    meeting_end = meeting_start + meeting_duration
    
    # Convert meeting_start and meeting_end to time strings
    def minutes_to_time(minutes):
        total_minutes = minutes
        hour = 9 + total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    start_time_str = minutes_to_time(meeting_start)
    end_time_str = minutes_to_time(meeting_end)
    
    # Format the output as HH:MM:HH:MM
    time_range_str = f"{start_time_str}:{end_time_str}"
    
    print("Monday")
    print(time_range_str)

if __name__ == "__main__":
    main()