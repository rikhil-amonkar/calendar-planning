def main():
    work_start = 0  # 9:00 in minutes from 9:00
    work_end = 480   # 17:00 in minutes (8 hours * 60)
    meeting_duration = 30
    preference_cutoff = 240  # 13:00 in minutes

    busy_intervals = []

    # Christine's busy intervals
    busy_intervals.append((30, 90))
    busy_intervals.append((180, 210))
    busy_intervals.append((240, 270))
    busy_intervals.append((330, 360))
    busy_intervals.append((420, 450))

    # Bobby's busy intervals
    busy_intervals.append((180, 210))
    busy_intervals.append((330, 360))

    # Elizabeth's busy intervals
    busy_intervals.append((0, 30))
    busy_intervals.append((150, 240))
    busy_intervals.append((270, 300))
    busy_intervals.append((360, 390))
    busy_intervals.append((420, 480))

    # Tyler's busy intervals
    busy_intervals.append((0, 120))
    busy_intervals.append((180, 210))
    busy_intervals.append((240, 270))
    busy_intervals.append((390, 420))
    busy_intervals.append((450, 480))

    # Edward's busy intervals
    busy_intervals.append((0, 30))
    busy_intervals.append((60, 120))
    busy_intervals.append((150, 240))
    busy_intervals.append((330, 390))
    busy_intervals.append((420, 480))

    # Sort intervals by start time
    busy_intervals.sort(key=lambda x: x[0])
    
    # Merge intervals
    merged = []
    if busy_intervals:
        current_start, current_end = busy_intervals[0]
        for i in range(1, len(busy_intervals)):
            s, e = busy_intervals[i]
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged.append((current_start, current_end))
                current_start, current_end = s, e
        merged.append((current_start, current_end))
    else:
        merged = []

    # Find free gaps
    free_gaps = []
    current = work_start
    for start, end in merged:
        if current < start:
            free_gaps.append((current, start))
        current = max(current, end)
    if current < work_end:
        free_gaps.append((current, work_end))

    # First, try to find a gap that ends by 13:00 (preference)
    candidate_start = None
    for gap in free_gaps:
        gap_start, gap_end = gap
        available_end = min(gap_end, preference_cutoff)
        if available_end - gap_start >= meeting_duration:
            candidate_start = gap_start
            break

    # If no preferred slot, find any gap of sufficient duration
    if candidate_start is None:
        for gap in free_gaps:
            gap_start, gap_end = gap
            if gap_end - gap_start >= meeting_duration:
                candidate_start = gap_start
                break

    # If still no slot found, we use the first gap (though problem states there is a solution)
    if candidate_start is None:
        candidate_start = free_gaps[0][0]  # fallback to the first gap start

    candidate_end = candidate_start + meeting_duration

    # Convert minutes back to time string
    start_hour = 9 + candidate_start // 60
    start_minute = candidate_start % 60
    end_hour = 9 + candidate_end // 60
    end_minute = candidate_end % 60

    start_str = f"{start_hour:02d}:{start_minute:02d}"
    end_str = f"{end_hour:02d}:{end_minute:02d}"
    time_range_str = f"{start_str}:{end_str}"

    print(f"Monday {{{time_range_str}}}")

if __name__ == "__main__":
    main()