def main():
    # Define work hours and meeting duration
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 30  # 30 minutes
    constraint_end = 15 * 60  # 15:00 in minutes (Bobby's constraint)

    # Convert time string to minutes
    def time_str_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        return hour * 60 + minute

    # Parse a meeting interval string
    def parse_interval(interval_str):
        parts = interval_str.split('-')
        start = time_str_to_minutes(parts[0])
        end = time_str_to_minutes(parts[1])
        return (start, end)

    # Busy intervals for each participant
    lisa_busy = ['9:00-10:00', '10:30-11:30', '12:30-13:00', '16:00-16:30']
    bobby_busy = ['9:00-9:30', '10:00-10:30', '11:30-12:00', '15:00-15:30']
    randy_busy = ['9:30-10:00', '10:30-11:00', '11:30-12:30', '13:00-13:30', '14:30-15:30', '16:00-16:30']

    # Convert busy intervals to minutes
    busy_lisa = [parse_interval(interval) for interval in lisa_busy]
    busy_bobby = [parse_interval(interval) for interval in bobby_busy]
    busy_randy = [parse_interval(interval) for interval in randy_busy]

    # Compute free intervals for a participant
    def compute_free_intervals(busy_intervals, start_time, end_time):
        if not busy_intervals:
            return [(start_time, end_time)]
        sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
        merged = []
        current_start, current_end = sorted_busy[0]
        for interval in sorted_busy[1:]:
            if interval[0] <= current_end:
                current_end = max(current_end, interval[1])
            else:
                merged.append((current_start, current_end))
                current_start, current_end = interval
        merged.append((current_start, current_end))
        
        free_intervals = []
        current = start_time
        for start, end in merged:
            if current < start:
                free_intervals.append((current, start))
            current = max(current, end)
        if current < end_time:
            free_intervals.append((current, end_time))
        return free_intervals

    # Compute free intervals for each participant
    free_lisa = compute_free_intervals(busy_lisa, work_start, work_end)
    free_bobby = compute_free_intervals(busy_bobby, work_start, work_end)
    free_randy = compute_free_intervals(busy_randy, work_start, work_end)

    # Find common free intervals
    common_free = free_lisa
    for free_list in [free_bobby, free_randy]:
        new_common = []
        for c_interval in common_free:
            for f_interval in free_list:
                start = max(c_interval[0], f_interval[0])
                end = min(c_interval[1], f_interval[1])
                if start < end:
                    new_common.append((start, end))
        common_free = new_common

    # Find the first meeting slot that fits the duration and constraint
    meeting_slot = None
    for s, e in common_free:
        available_end = min(e, constraint_end)
        if available_end - s >= meeting_duration:
            meeting_slot = (s, s + meeting_duration)
            break

    # Convert meeting slot to time strings
    def minutes_to_time(minutes):
        hour = minutes // 60
        minute = minutes % 60
        return f"{hour:02d}:{minute:02d}"

    start_time_str = minutes_to_time(meeting_slot[0])
    end_time_str = minutes_to_time(meeting_slot[1])
    time_range_str = f"{start_time_str}:{end_time_str}"

    # Output the day and time range
    print("Monday")
    print(time_range_str)

if __name__ == "__main__":
    main()