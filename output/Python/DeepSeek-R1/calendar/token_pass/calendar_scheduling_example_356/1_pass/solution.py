def main():
    # Convert time string to minutes past 9:00
    def time_to_minutes(t):
        h, m = map(int, t.split(':'))
        return (h - 9) * 60 + m

    # Convert minutes back to time string
    def minutes_to_time(m):
        h = 9 + m // 60
        m = m % 60
        return f"{h:02d}:{m:02d}"

    # Work day from 9:00 to 17:00 (480 minutes)
    day_start = 0
    day_end = 480

    # Collect all busy intervals in minutes
    busy_intervals = []
    
    # Katherine
    busy_intervals.append((time_to_minutes("12:00"), time_to_minutes("12:30")))
    busy_intervals.append((time_to_minutes("13:00"), time_to_minutes("14:30")))
    
    # Julie
    busy_intervals.append((time_to_minutes("9:00"), time_to_minutes("9:30")))
    busy_intervals.append((time_to_minutes("10:30"), time_to_minutes("11:00")))
    busy_intervals.append((time_to_minutes("13:30"), time_to_minutes("14:00")))
    busy_intervals.append((time_to_minutes("15:00"), time_to_minutes("15:30")))
    
    # Angela
    busy_intervals.append((time_to_minutes("9:00"), time_to_minutes("10:00")))
    busy_intervals.append((time_to_minutes("10:30"), time_to_minutes("11:00")))
    busy_intervals.append((time_to_minutes("11:30"), time_to_minutes("14:00")))
    busy_intervals.append((time_to_minutes("14:30"), time_to_minutes("15:00")))
    busy_intervals.append((time_to_minutes("16:30"), time_to_minutes("17:00")))
    
    # Nicholas
    busy_intervals.append((time_to_minutes("9:30"), time_to_minutes("11:00")))
    busy_intervals.append((time_to_minutes("11:30"), time_to_minutes("13:30")))
    busy_intervals.append((time_to_minutes("14:00"), time_to_minutes("16:00")))
    busy_intervals.append((time_to_minutes("16:30"), time_to_minutes("17:00")))
    
    # Carl
    busy_intervals.append((time_to_minutes("9:00"), time_to_minutes("11:00")))
    busy_intervals.append((time_to_minutes("11:30"), time_to_minutes("12:30")))
    busy_intervals.append((time_to_minutes("13:00"), time_to_minutes("14:30")))
    busy_intervals.append((time_to_minutes("15:00"), time_to_minutes("16:00")))
    busy_intervals.append((time_to_minutes("16:30"), time_to_minutes("17:00")))

    # Merge busy intervals
    busy_intervals.sort(key=lambda x: x[0])
    merged = []
    start, end = busy_intervals[0]
    for interval in busy_intervals[1:]:
        if interval[0] <= end:
            end = max(end, interval[1])
        else:
            merged.append((start, end))
            start, end = interval
    merged.append((start, end))

    # Find free intervals
    free_intervals = []
    current = day_start
    for start, end in merged:
        if current < start:
            free_intervals.append((current, start))
        current = end
    if current < day_end:
        free_intervals.append((current, day_end))

    # Find meeting slot (30 minutes)
    meeting_duration = 30
    preferred_start = time_to_minutes("15:00")  # 360 minutes from 9:00

    candidate_after = None
    candidate_before = None

    for start, end in free_intervals:
        # Check if interval is entirely after 15:00
        if start >= preferred_start:
            if end - start >= meeting_duration:
                candidate_after = (start, start + meeting_duration)
                break
        # Check if interval spans 15:00
        elif start < preferred_start < end:
            available_after = end - preferred_start
            if available_after >= meeting_duration:
                candidate_after = (preferred_start, preferred_start + meeting_duration)
                break
        # Check intervals entirely before 15:00
        else:
            if end - start >= meeting_duration and candidate_before is None:
                candidate_before = (start, start + meeting_duration)

    # Select candidate
    if candidate_after:
        meeting_start, meeting_end = candidate_after
    elif candidate_before:
        meeting_start, meeting_end = candidate_before
    else:
        return

    # Convert back to time strings
    meeting_start_str = minutes_to_time(meeting_start)
    meeting_end_str = minutes_to_time(meeting_end)
    
    print(f"Monday {meeting_start_str}:{meeting_end_str}")

if __name__ == "__main__":
    main()