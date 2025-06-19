def main():
    # Define work hours: 9:00 to 17:00 (8 hours = 480 minutes)
    work_start = 0   # 9:00 in minutes from 9:00
    work_end = 480   # 17:00

    # Busy intervals in minutes (relative to 9:00)
    raymond_busy = [[0, 30], [150, 180], [240, 270], [360, 390]]
    billy_busy = [[60, 90], [180, 240], [450, 480]]
    donald_busy = [[0, 30], [60, 120], [180, 240], [300, 330], [420, 480]]

    # Function to compute free intervals given busy intervals and work hours
    def get_free_intervals(busy_intervals, start, end):
        if not busy_intervals:
            return [[start, end]]
        sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
        free = []
        current = start
        for interval in sorted_busy:
            s, e = interval
            if current < s:
                free.append([current, s])
            current = max(current, e)
        if current < end:
            free.append([current, end])
        return free

    # Function to intersect two sets of intervals
    def intersect_intervals(intervals1, intervals2):
        if not intervals1 or not intervals2:
            return []
        i, j = 0, 0
        result = []
        while i < len(intervals1) and j < len(intervals2):
            a1, a2 = intervals1[i]
            b1, b2 = intervals2[j]
            start = max(a1, b1)
            end = min(a2, b2)
            if start < end:
                result.append([start, end])
            if a2 < b2:
                i += 1
            else:
                j += 1
        return result

    # Calculate free intervals for each person
    raymond_free = get_free_intervals(raymond_busy, work_start, work_end)
    billy_free = get_free_intervals(billy_busy, work_start, work_end)
    donald_free = get_free_intervals(donald_busy, work_start, work_end)

    # Find common free intervals
    common_free = intersect_intervals(raymond_free, billy_free)
    common_free = intersect_intervals(common_free, donald_free)

    # Find the earliest 30-minute slot that starts before 15:00 (360 minutes) if available
    candidate = None
    for interval in common_free:
        start, end = interval
        if start + 30 <= end:
            if start < 360:  # Meeting starts before 15:00
                candidate = [start, start + 30]
                break
    if candidate is None:
        for interval in common_free:
            start, end = interval
            if start + 30 <= end:
                candidate = [start, start + 30]
                break

    # Convert candidate from minutes to time strings
    def minutes_to_time(minutes):
        total_minutes = minutes
        hours = 9 + total_minutes // 60
        mins = total_minutes % 60
        return f"{hours:02d}:{mins:02d}"

    start_time = minutes_to_time(candidate[0])
    end_time = minutes_to_time(candidate[1])
    
    # Output the time range and day
    print(f"{start_time}:{end_time}")
    print("Monday")

if __name__ == "__main__":
    main()