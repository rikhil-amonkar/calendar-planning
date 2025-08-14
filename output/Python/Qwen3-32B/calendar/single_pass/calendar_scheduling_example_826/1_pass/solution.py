def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours:02d}:{mins:02d}"

def find_meeting_time():
    work_start = 9 * 60
    work_end = 17 * 60
    busy_times = {
        'Monday': [
            (540, 570),
            (630, 660),
            (750, 780),
            (870, 930),
            (990, 1020),
        ],
        'Tuesday': [
            (540, 660),
            (690, 720),
            (750, 930),
            (960, 1020),
        ],
        'Wednesday': [
            (600, 660),
            (720, 780),
            (810, 960),
        ],
        'Thursday': [
            (570, 690),
            (720, 750),
            (780, 810),
            (840, 870),
            (990, 1020),
        ],
    }

    days_order = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    for day in days_order:
        busy_intervals = busy_times[day]
        # Generate free slots
        free_slots = []
        prev_end = work_start
        # Sort busy intervals
        busy_intervals.sort()
        for start, end in busy_intervals:
            if start > prev_end:
                free_slots.append( (prev_end, start) )
            prev_end = max(prev_end, end)
        if prev_end < work_end:
            free_slots.append( (prev_end, work_end) )
        # Check each free slot
        for s, e in free_slots:
            if e - s >= 30:
                start_time = s
                end_time = s + 30
                start_str = minutes_to_time(start_time)
                end_str = minutes_to_time(end_time)
                return f"{start_str}:{end_str} {day}"
    return "No solution found"

if __name__ == "__main__":
    result = find_meeting_time()
    print(result)