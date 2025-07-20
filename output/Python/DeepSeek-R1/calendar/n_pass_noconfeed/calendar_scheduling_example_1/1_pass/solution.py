def main():
    # Work hours: 9:00 to 17:00 (converted to minutes from midnight)
    work_start = 9 * 60  # 540 minutes
    work_end = 17 * 60   # 1020 minutes
    meeting_duration = 30  # minutes
    # Preference: Billy wants to avoid meetings after 15:00 -> 15:00 is 900 minutes
    preference_deadline = 15 * 60  # 900 minutes (end of meeting must be <= 900 to satisfy preference)

    # Busy intervals for each participant (given as strings)
    raymond_busy = [
        ("9:00", "9:30"),
        ("11:30", "12:00"),
        ("13:00", "13:30"),
        ("15:00", "15:30")
    ]
    billy_busy = [
        ("10:00", "10:30"),
        ("12:00", "13:00"),
        ("16:30", "17:00")
    ]
    donald_busy = [
        ("9:00", "9:30"),
        ("10:00", "11:00"),
        ("12:00", "13:00"),
        ("14:00", "14:30"),
        ("16:00", "17:00")
    ]

    # Convert time string to minutes
    def time_str_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        return hour * 60 + minute

    # Convert busy intervals to minutes
    def convert_busy_list(busy_list):
        return [(time_str_to_minutes(s), time_str_to_minutes(e)) for s, e in busy_list]

    raymond_busy_min = convert_busy_list(raymond_busy)
    billy_busy_min = convert_busy_list(billy_busy)
    donald_busy_min = convert_busy_list(donald_busy)

    # Generate free intervals within work hours
    def get_free_intervals(busy_intervals, work_start, work_end):
        if not busy_intervals:
            return [(work_start, work_end)]
        sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
        free = []
        current = work_start
        for start, end in sorted_busy:
            if current < start:
                free.append((current, start))
            current = max(current, end)
        if current < work_end:
            free.append((current, work_end))
        return free

    raymond_free = get_free_intervals(raymond_busy_min, work_start, work_end)
    billy_free = get_free_intervals(billy_busy_min, work_start, work_end)
    donald_free = get_free_intervals(donald_busy_min, work_start, work_end)

    # Find common free intervals by intersecting two sets at a time
    def intersect_two_intervals(intervals1, intervals2):
        i = j = 0
        result = []
        while i < len(intervals1) and j < len(intervals2):
            start = max(intervals1[i][0], intervals2[j][0])
            end = min(intervals1[i][1], intervals2[j][1])
            if start < end:
                result.append((start, end))
            if intervals1[i][1] < intervals2[j][1]:
                i += 1
            else:
                j += 1
        return result

    common_free = intersect_two_intervals(raymond_free, billy_free)
    common_free = intersect_two_intervals(common_free, donald_free)

    # Sort common free intervals by start time
    common_free_sorted = sorted(common_free, key=lambda x: x[0])

    # Find the earliest meeting start time that satisfies the preference (ends by 15:00)
    chosen_start = None
    for s, e in common_free_sorted:
        if e - s < meeting_duration:
            continue
        # Check if we can schedule a meeting starting at 's' that ends by 15:00
        if s + meeting_duration <= min(e, preference_deadline):
            chosen_start = s
            break

    # If no preferred slot, find any available slot
    if chosen_start is None:
        for s, e in common_free_sorted:
            if e - s >= meeting_duration:
                chosen_start = s
                break

    # Convert chosen_start back to time string
    def minutes_to_time_str(minutes):
        hour = minutes // 60
        minute = minutes % 60
        return f"{hour:02d}:{minute:02d}"

    start_str = minutes_to_time_str(chosen_start)
    end_str = minutes_to_time_str(chosen_start + meeting_duration)
    time_range_str = f"{start_str}:{end_str}"

    # Output the day and time range
    print("Monday")
    print(time_range_str)

if __name__ == "__main__":
    main()