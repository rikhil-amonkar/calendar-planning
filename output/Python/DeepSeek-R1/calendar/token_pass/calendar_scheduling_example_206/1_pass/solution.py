def main():
    # Convert time string to minutes since 9:00
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return (hours - 9) * 60 + minutes

    # Convert minutes since 9:00 back to time string
    def minutes_to_time(minutes):
        total_minutes = 9 * 60 + minutes
        hours = total_minutes // 60
        mins = total_minutes % 60
        return f"{hours:02d}:{mins:02d}"

    # Work hours: 9:00 to 17:00 (480 minutes)
    work_start = 0
    work_end = 480
    meeting_duration = 30
    margaret_constraint = time_to_minutes('14:30')  # 330 minutes

    # Busy intervals for each participant (in minutes since 9:00)
    busy_intervals = [
        # Shirley
        [(time_to_minutes('10:30'), time_to_minutes('11:00')),
         (time_to_minutes('12:00'), time_to_minutes('12:30'))],
        # Jacob
        [(time_to_minutes('9:00'), time_to_minutes('9:30')),
         (time_to_minutes('10:00'), time_to_minutes('10:30')),
         (time_to_minutes('11:00'), time_to_minutes('11:30')),
         (time_to_minutes('12:30'), time_to_minutes('13:30')),
         (time_to_minutes('14:30'), time_to_minutes('15:00'))],
        # Stephen
        [(time_to_minutes('11:30'), time_to_minutes('12:00')),
         (time_to_minutes('12:30'), time_to_minutes('13:00'))],
        # Margaret
        [(time_to_minutes('9:00'), time_to_minutes('9:30')),
         (time_to_minutes('10:30'), time_to_minutes('12:30')),
         (time_to_minutes('13:00'), time_to_minutes('13:30')),
         (time_to_minutes('15:00'), time_to_minutes('15:30')),
         (time_to_minutes('16:30'), time_to_minutes('17:00'))],
        # Mason
        [(time_to_minutes('9:00'), time_to_minutes('10:00')),
         (time_to_minutes('10:30'), time_to_minutes('11:00')),
         (time_to_minutes('11:30'), time_to_minutes('12:30')),
         (time_to_minutes('13:00'), time_to_minutes('13:30')),
         (time_to_minutes('14:00'), time_to_minutes('14:30')),
         (time_to_minutes('16:30'), time_to_minutes('17:00'))]
    ]

    # Combine all busy intervals
    all_busy = []
    for intervals in busy_intervals:
        all_busy.extend(intervals)
    
    # Sort intervals by start time
    all_busy.sort(key=lambda x: x[0])
    
    # Merge intervals
    merged = []
    for start, end in all_busy:
        if not merged:
            merged.append([start, end])
        else:
            last_end = merged[-1][1]
            if start <= last_end:
                merged[-1][1] = max(last_end, end)
            else:
                merged.append([start, end])
    
    # Find free intervals within work hours
    free_intervals = []
    current = work_start
    for start, end in merged:
        if current < start:
            free_intervals.append((current, start))
        current = max(current, end)
    if current < work_end:
        free_intervals.append((current, work_end))
    
    # Find first free interval that meets duration and Margaret's constraint
    for start, end in free_intervals:
        if start >= margaret_constraint and end - start >= meeting_duration:
            meeting_start = start
            meeting_end = meeting_start + meeting_duration
            start_str = minutes_to_time(meeting_start)
            end_str = minutes_to_time(meeting_end)
            print(f"Monday\n{start_str}:{end_str}")
            return
    
    print("No suitable time found")

if __name__ == "__main__":
    main()