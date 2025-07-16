def main():
    day = "Monday"
    work_start = 9 * 60  # 09:00 in minutes
    work_end = 15 * 60   # 15:00 in minutes (due to Helen's constraint)
    
    # Christine's busy intervals (start, end) in minutes, represented as half-open [start, end)
    christine_busy = [
        (11 * 60, 11 * 60 + 30),  # 11:00-11:30
    ]
    
    # Helen's busy intervals (start, end) in minutes within [work_start, work_end)
    helen_busy = [
        (9 * 60 + 30, 10 * 60 + 30),  # 09:30-10:30
        (11 * 60, 11 * 60 + 30),       # 11:00-11:30
        (12 * 60, 12 * 60 + 30),       # 12:00-12:30
        (13 * 60 + 30, 15 * 60)        # 13:30-15:00
    ]
    
    # Combine all busy intervals
    all_busy = christine_busy + helen_busy
    all_busy_sorted = sorted(all_busy, key=lambda x: x[0])
    
    # Merge overlapping intervals
    merged = []
    if all_busy_sorted:
        current_start, current_end = all_busy_sorted[0]
        for s, e in all_busy_sorted[1:]:
            if s <= current_end:  # Overlapping or adjacent
                current_end = max(current_end, e)
            else:
                merged.append((current_start, current_end))
                current_start, current_end = s, e
        merged.append((current_start, current_end))
    
    # Find free gaps
    current = work_start
    free_gaps = []
    for s, e in merged:
        if current < s:
            free_gaps.append((current, s))
        current = max(current, e)
    if current < work_end:
        free_gaps.append((current, work_end))
    
    # Find the first free gap of at least 30 minutes
    meeting_start = None
    meeting_end = None
    for start_gap, end_gap in free_gaps:
        gap_duration = end_gap - start_gap
        if gap_duration >= 30:
            meeting_start = start_gap
            meeting_end = start_gap + 30
            break
    
    # Convert meeting time to HH:MM format
    def minutes_to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"
    
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    
    # Output day and time range in specified format
    print(day)
    print(f"{{{start_str}:{end_str}}}")

if __name__ == "__main__":
    main()