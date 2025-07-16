def main():
    # Convert time to minutes from 9:00
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return (hours - 9) * 60 + minutes

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        total_minutes = minutes
        hours = 9 + total_minutes // 60
        mins = total_minutes % 60
        return f"{hours:02d}:{mins:02d}"

    # Busy intervals for Tuesday (converted to minutes from 9:00)
    jesse_busy = [
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:00"), time_to_minutes("15:00"))
    ]
    lawrence_busy = [
        (time_to_minutes("9:30"), time_to_minutes("10:30")),
        (time_to_minutes("11:30"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:30"))  # 16:30 is 450 minutes
    ]
    
    # Work hours: 9:00 to 17:00 (480 minutes) for Jesse, but Lawrence only until 16:30 (450 minutes)
    work_end_jesse = time_to_minutes("17:00")
    work_end_lawrence = time_to_minutes("16:30")
    
    # Compute free intervals
    def get_free_intervals(busy_intervals, work_end):
        busy_sorted = sorted(busy_intervals, key=lambda x: x[0])
        free = []
        current = 0  # work starts at 9:00 (0 minutes)
        for start, end in busy_sorted:
            if current < start:
                free.append((current, start))
            current = max(current, end)
        if current < work_end:
            free.append((current, work_end))
        return free

    jesse_free = get_free_intervals(jesse_busy, work_end_jesse)
    lawrence_free = get_free_intervals(lawrence_busy, work_end_lawrence)
    
    # Find earliest overlapping 30-minute slot
    meeting_start = None
    for j_start, j_end in jesse_free:
        for l_start, l_end in lawrence_free:
            start_overlap = max(j_start, l_start)
            end_overlap = min(j_end, l_end)
            if end_overlap - start_overlap >= 30:
                meeting_start = start_overlap
                break
        if meeting_start is not None:
            break
    
    # Convert to time strings
    start_time = minutes_to_time(meeting_start)
    end_time = minutes_to_time(meeting_start + 30)
    
    # Output day and time in specified format
    print("Tuesday")
    print(f"{start_time}:{end_time}")

if __name__ == "__main__":
    main()