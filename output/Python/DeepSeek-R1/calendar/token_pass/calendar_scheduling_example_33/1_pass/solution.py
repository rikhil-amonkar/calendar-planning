def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    meeting_duration = 30
    avoid_after = time_to_minutes("15:00")  # Bobby's preference to avoid after 15:00

    # Define busy intervals for each person as half-open [start, end)
    lisa_busy = [
        [time_to_minutes("9:00"), time_to_minutes("10:00")],
        [time_to_minutes("10:30"), time_to_minutes("11:30")],
        [time_to_minutes("12:30"), time_to_minutes("13:00")],
        [time_to_minutes("16:00"), time_to_minutes("16:30")]
    ]
    bobby_busy = [
        [time_to_minutes("9:00"), time_to_minutes("9:30")],
        [time_to_minutes("10:00"), time_to_minutes("10:30")],
        [time_to_minutes("11:30"), time_to_minutes("12:00")],
        [time_to_minutes("15:00"), time_to_minutes("15:30")]
    ]
    randy_busy = [
        [time_to_minutes("9:30"), time_to_minutes("10:00")],
        [time_to_minutes("10:30"), time_to_minutes("11:00")],
        [time_to_minutes("11:30"), time_to_minutes("12:30")],
        [time_to_minutes("13:00"), time_to_minutes("13:30")],
        [time_to_minutes("14:30"), time_to_minutes("15:30")],
        [time_to_minutes("16:00"), time_to_minutes("16:30")]
    ]

    # Combine all busy intervals
    all_busy = lisa_busy + bobby_busy + randy_busy
    all_busy.sort(key=lambda x: x[0])

    # Merge intervals
    merged = []
    start, end = all_busy[0]
    for interval in all_busy[1:]:
        if interval[0] < end:
            end = max(end, interval[1])
        else:
            merged.append([start, end])
            start, end = interval
    merged.append([start, end])

    # Find free intervals within work hours
    free_intervals = []
    current = work_start
    for busy in merged:
        if current < busy[0]:
            free_intervals.append([current, busy[0]])
        current = max(current, busy[1])
    if current < work_end:
        free_intervals.append([current, work_end])

    # Find a suitable free interval
    chosen_start = None
    for interval in free_intervals:
        start, end = interval
        # Check if the interval is long enough
        if end - start >= meeting_duration:
            # Check if the entire interval is before avoid_after time
            if end <= avoid_after:
                chosen_start = start
                break
            # If not entirely before, check if we can schedule before avoid_after
            if start < avoid_after:
                if avoid_after - start >= meeting_duration:
                    chosen_start = start
                    break
    # If no suitable interval before avoid_after, take the first long enough interval
    if chosen_start is None:
        for interval in free_intervals:
            start, end = interval
            if end - start >= meeting_duration:
                chosen_start = start
                break

    meeting_end = chosen_start + meeting_duration
    meeting_start_str = minutes_to_time(chosen_start)
    meeting_end_str = minutes_to_time(meeting_end)
    
    print(f"Monday {meeting_start_str}:{meeting_end_str}")

if __name__ == "__main__":
    main()