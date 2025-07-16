def main():
    # Convert time string to minutes since 9:00
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        return (hour - 9) * 60 + minute

    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        total_minutes = minutes
        hour = 9 + total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"

    # Work day: 9:00 (0 min) to 17:00 (480 min)
    day_end = 480

    # Billy's constraint: meeting must end by 15:00 (360 min)
    constraint_end = 360

    # Busy intervals in minutes (each as [start, end), exclusive end)
    raymond_busy = [
        [time_to_minutes('9:00'), time_to_minutes('9:30')],
        [time_to_minutes('11:30'), time_to_minutes('12:00')],
        [time_to_minutes('13:00'), time_to_minutes('13:30')],
        [time_to_minutes('15:00'), time_to_minutes('15:30')]
    ]
    billy_busy = [
        [time_to_minutes('10:00'), time_to_minutes('10:30')],
        [time_to_minutes('12:00'), time_to_minutes('13:00')],
        [time_to_minutes('16:30'), time_to_minutes('17:00')]
    ]
    donald_busy = [
        [time_to_minutes('9:00'), time_to_minutes('9:30')],
        [time_to_minutes('10:00'), time_to_minutes('11:00')],
        [time_to_minutes('12:00'), time_to_minutes('13:00')],
        [time_to_minutes('14:00'), time_to_minutes('14:30')],
        [time_to_minutes('16:00'), time_to_minutes('17:00')]
    ]

    # Compute free intervals for a participant
    def get_free_intervals(busy_intervals):
        busy_intervals.sort(key=lambda x: x[0])
        free = []
        current_start = 0
        for interval in busy_intervals:
            if current_start < interval[0]:
                free.append([current_start, interval[0]])
            current_start = interval[1]
        if current_start < day_end:
            free.append([current_start, day_end])
        return free

    # Compute free intervals for each participant
    free_raymond = get_free_intervals(raymond_busy)
    free_billy = get_free_intervals(billy_busy)
    free_donald = get_free_intervals(donald_busy)

    # Find common free intervals between two sets
    def intersect_intervals(intervals1, intervals2):
        i, j = 0, 0
        result = []
        while i < len(intervals1) and j < len(intervals2):
            low = max(intervals1[i][0], intervals2[j][0])
            high = min(intervals1[i][1], intervals2[j][1])
            if low < high:
                result.append([low, high])
            if intervals1[i][1] < intervals2[j][1]:
                i += 1
            else:
                j += 1
        return result

    # Common free for all three
    common_raymond_billy = intersect_intervals(free_raymond, free_billy)
    common_all = intersect_intervals(common_raymond_billy, free_donald)

    # Find the earliest 30-minute slot that ends by constraint_end (360 min)
    meeting_duration = 30
    slot_found = None
    for interval in common_all:
        start, end = interval
        # The latest start time to meet the constraint
        max_start = constraint_end - meeting_duration
        if max_start < start:
            continue
        # The available start range in this interval
        slot_start = start
        slot_end = slot_start + meeting_duration
        if slot_end <= end and slot_end <= constraint_end:
            slot_found = (slot_start, slot_end)
            break

    if slot_found:
        start_min, end_min = slot_found
        start_time = minutes_to_time(start_min)
        end_time = minutes_to_time(end_min)
        # Format as HH:MM:HH:MM
        time_range_str = f"{start_time.replace(':', '')[:2]}:{start_time[-2:]}:{end_time.replace(':', '')[:2]}:{end_time[-2:]}"
        print(time_range_str)
        print("Monday")

if __name__ == "__main__":
    main()