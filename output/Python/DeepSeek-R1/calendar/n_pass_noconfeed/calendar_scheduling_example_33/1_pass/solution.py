def main():
    # Work hours: 9:00 to 17:00 (Monday)
    work_start = 9 * 60  # 540 minutes
    work_end = 17 * 60   # 1020 minutes
    # Bobby's preference: avoid after 15:00 (900 minutes)
    avoid_after = 15 * 60
    meeting_duration = 30  # minutes

    # Busy intervals in minutes (start, end)
    lisa_busy = [
        [540, 600],   # 9:00-10:00
        [630, 690],   # 10:30-11:30
        [750, 780],   # 12:30-13:00
        [960, 990]    # 16:00-16:30
    ]
    bobby_busy = [
        [540, 570],   # 9:00-9:30
        [600, 630],   # 10:00-10:30
        [690, 720],   # 11:30-12:00
        [900, 930]    # 15:00-15:30
    ]
    randy_busy = [
        [570, 600],   # 9:30-10:00
        [630, 660],   # 10:30-11:00
        [690, 750],   # 11:30-12:30
        [780, 810],   # 13:00-13:30
        [870, 900],   # 14:30-15:30
        [960, 990]    # 16:00-16:30
    ]

    # Function to compute free intervals
    def get_free_intervals(busy_list, start_bound, end_bound):
        if not busy_list:
            return [[start_bound, end_bound]]
        sorted_busy = sorted(busy_list, key=lambda x: x[0])
        free = []
        current_start = start_bound
        for interval in sorted_busy:
            s, e = interval
            if current_start < s:
                free.append([current_start, s])
            current_start = max(current_start, e)
        if current_start < end_bound:
            free.append([current_start, end_bound])
        return free

    # Get free intervals for each
    lisa_free = get_free_intervals(lisa_busy, work_start, work_end)
    bobby_free = get_free_intervals(bobby_busy, work_start, work_end)
    randy_free = get_free_intervals(randy_busy, work_start, work_end)

    # Function to intersect two sets of intervals
    def intersect_two(intervals_a, intervals_b):
        i = j = 0
        result = []
        while i < len(intervals_a) and j < len(intervals_b):
            a = intervals_a[i]
            b = intervals_b[j]
            start_max = max(a[0], b[0])
            end_min = min(a[1], b[1])
            if start_max < end_min:
                result.append([start_max, end_min])
            if a[1] < b[1]:
                i += 1
            else:
                j += 1
        return result

    # Find common free intervals
    common_free = intersect_two(lisa_free, bobby_free)
    common_free = intersect_two(common_free, randy_free)
    
    candidate = None
    # First pass: find slot ending by avoid_after (900)
    for interval in common_free:
        start, end = interval
        # Latest start time for meeting to end by avoid_after
        latest_start = min(end, avoid_after) - meeting_duration
        if start <= latest_start:
            candidate = (start, start + meeting_duration)
            break
    
    # Second pass: if no preferred slot, find any 30-minute slot
    if candidate is None:
        for interval in common_free:
            start, end = interval
            if end - start >= meeting_duration:
                candidate = (start, start + meeting_duration)
                break

    # Convert candidate to time string
    def format_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"
    
    start_time = format_time(candidate[0])
    end_time = format_time(candidate[1])
    time_str = f"{start_time}:{end_time}"

    # Output day and time
    print("Monday")
    print(time_str)

if __name__ == "__main__":
    main()