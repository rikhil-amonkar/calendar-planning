def main():
    # Convert time string to minutes from 9:00
    def time_to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return (h - 9) * 60 + m

    # Convert minutes from 9:00 back to absolute time (HH, MM)
    def minutes_to_time(mins):
        total_minutes = 9 * 60 + mins
        h = total_minutes // 60
        m = total_minutes % 60
        return h, m

    # Collect all busy intervals
    busy_intervals = []
    
    # Emily's meetings
    busy_intervals.append((time_to_minutes('10:00'), time_to_minutes('10:30')))
    busy_intervals.append((time_to_minutes('16:00'), time_to_minutes('16:30')))
    
    # Maria's meetings
    busy_intervals.append((time_to_minutes('10:30'), time_to_minutes('11:00')))
    busy_intervals.append((time_to_minutes('14:00'), time_to_minutes('14:30')))
    
    # Carl's meetings
    busy_intervals.append((time_to_minutes('9:30'), time_to_minutes('10:00')))
    busy_intervals.append((time_to_minutes('10:30'), time_to_minutes('12:30')))
    busy_intervals.append((time_to_minutes('13:30'), time_to_minutes('14:00')))
    busy_intervals.append((time_to_minutes('14:30'), time_to_minutes('15:30')))
    busy_intervals.append((time_to_minutes('16:00'), time_to_minutes('17:00')))
    
    # David's meetings
    busy_intervals.append((time_to_minutes('9:30'), time_to_minutes('11:00')))
    busy_intervals.append((time_to_minutes('11:30'), time_to_minutes('12:00')))
    busy_intervals.append((time_to_minutes('12:30'), time_to_minutes('13:30')))
    busy_intervals.append((time_to_minutes('14:00'), time_to_minutes('15:00')))
    busy_intervals.append((time_to_minutes('16:00'), time_to_minutes('17:00')))
    
    # Frank's meetings
    busy_intervals.append((time_to_minutes('9:30'), time_to_minutes('10:30')))
    busy_intervals.append((time_to_minutes('11:00'), time_to_minutes('11:30')))
    busy_intervals.append((time_to_minutes('12:30'), time_to_minutes('13:30')))
    busy_intervals.append((time_to_minutes('14:30'), time_to_minutes('17:00')))
    
    # Sort intervals by start time
    busy_intervals.sort(key=lambda x: x[0])
    
    # Merge overlapping intervals
    merged = []
    if busy_intervals:
        current_start, current_end = busy_intervals[0]
        for s, e in busy_intervals[1:]:
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged.append((current_start, current_end))
                current_start, current_end = s, e
        merged.append((current_start, current_end))
    
    # Find free intervals (work hours: 0 to 480 minutes)
    free_intervals = []
    start_free = 0
    for interval in merged:
        s, e = interval
        if start_free < s:
            free_intervals.append((start_free, s))
        start_free = e
    if start_free < 480:
        free_intervals.append((start_free, 480))
    
    # Find the first free interval that can fit 30 minutes
    for s, e in free_intervals:
        if e - s >= 30:
            slot_start = s
            slot_end = s + 30
            break
    
    # Convert slot to time strings
    start_h, start_m = minutes_to_time(slot_start)
    end_h, end_m = minutes_to_time(slot_end)
    
    # Format and output
    day = "Monday"
    time_str = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
    print(day)
    print(time_str)

if __name__ == "__main__":
    main()