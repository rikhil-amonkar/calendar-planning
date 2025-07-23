def get_free_intervals(busy_intervals, day_start, day_end):
    if not busy_intervals:
        return [(day_start, day_end)]
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current_start = day_start
    for s, e in sorted_busy:
        if current_start < s:
            free.append((current_start, s))
        current_start = max(current_start, e)
    if current_start < day_end:
        free.append((current_start, day_end))
    return free

def intersect_intervals(intervals1, intervals2):
    if not intervals1 or not intervals2:
        return []
    i = j = 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        low = max(intervals1[i][0], intervals2[j][0])
        high = min(intervals1[i][1], intervals2[j][1])
        if low < high:
            result.append((low, high))
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return result

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    day_start = 540   # 9:00 in minutes
    day_end = 1020    # 17:00 in minutes
    meeting_duration = 30

    # Define busy intervals in minutes (start, end)
    eric_busy = []
    ashley_busy = [
        (10*60, 10*60+30),   # 10:00-10:30
        (11*60, 12*60),       # 11:00-12:00
        (12*60+30, 13*60),    # 12:30-13:00
        (15*60, 16*60)        # 15:00-16:00
    ]
    ronald_busy = [
        (9*60, 9*60+30),      # 9:00-9:30
        (10*60, 11*60+30),    # 10:00-11:30
        (12*60+30, 14*60),    # 12:30-14:00
        (14*60+30, 17*60)     # 14:30-17:00
    ]
    larry_busy = [
        (9*60, 12*60),        # 9:00-12:00
        (13*60, 17*60)        # 13:00-17:00
    ]

    # Compute free intervals
    free_eric = get_free_intervals(eric_busy, day_start, day_end)
    free_ashley = get_free_intervals(ashley_busy, day_start, day_end)
    free_ronald = get_free_intervals(ronald_busy, day_start, day_end)
    free_larry = get_free_intervals(larry_busy, day_start, day_end)

    # Find common free intervals
    common_free = intersect_intervals(free_eric, free_ashley)
    common_free = intersect_intervals(common_free, free_ronald)
    common_free = intersect_intervals(common_free, free_larry)

    # Find the first slot of at least meeting_duration
    meeting_start = None
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            break

    if meeting_start is None:
        print("No suitable time found")
        return

    # Convert to time strings
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    time_range_str = f"{start_str}:{end_str}"

    # Output day and time range
    print("Monday")
    print(time_range_str)

if __name__ == "__main__":
    main()