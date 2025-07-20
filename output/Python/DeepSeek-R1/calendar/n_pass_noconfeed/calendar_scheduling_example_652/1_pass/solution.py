def main():
    # Define work hours: 9:00 to 17:00 (480 minutes from 9:00)
    work_start = 0      # 9:00 in minutes since 9:00
    work_end = 480      # 17:00 in minutes since 9:00
    meeting_duration = 30
    lawrence_end_constraint = 450  # 16:30 in minutes since 9:00

    # Jesse's Tuesday meetings in minutes since 9:00
    jesse_tue = [
        (0, 30),    # 9:00-9:30
        (240, 270), # 13:00-13:30
        (300, 360)  # 14:00-15:00
    ]

    # Lawrence's Tuesday meetings in minutes since 9:00
    lawrence_tue = [
        (30, 90),    # 9:30-10:30
        (150, 210),  # 11:30-12:30
        (240, 270),  # 13:00-13:30
        (330, 360),  # 14:30-15:00
        (390, 450)   # 15:30-16:30
    ]

    # Combine all busy intervals for Tuesday
    busy_all = jesse_tue + lawrence_tue
    busy_all_sorted = sorted(busy_all, key=lambda x: x[0])

    # Merge overlapping intervals
    merged = []
    if busy_all_sorted:
        current_start, current_end = busy_all_sorted[0]
        for i in range(1, len(busy_all_sorted)):
            s, e = busy_all_sorted[i]
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged.append((current_start, current_end))
                current_start, current_end = s, e
        merged.append((current_start, current_end))

    # Compute free intervals within work hours
    free_intervals = []
    start = work_start
    for interval in merged:
        if start < interval[0]:
            free_intervals.append((start, interval[0]))
        start = max(start, interval[1])
    if start < work_end:
        free_intervals.append((start, work_end))

    # Find the earliest 30-minute slot that ends by lawrence_end_constraint
    candidate = None
    for a, b in free_intervals:
        latest_possible_end = min(b, lawrence_end_constraint)
        if a + meeting_duration <= latest_possible_end:
            candidate = (a, a + meeting_duration)
            break

    # Convert candidate to time strings
    if candidate is None:
        # According to the problem, a solution exists, so this is a fallback
        print("No solution found")
    else:
        start_min, end_min = candidate
        # Convert start_min to time
        start_hour = 9 + start_min // 60
        start_minute = start_min % 60
        # Convert end_min to time
        end_hour = 9 + end_min // 60
        end_minute = end_min % 60
        
        # Format as HH:MM:HH:MM
        time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        print(f"Tuesday {time_str}")

if __name__ == "__main__":
    main()