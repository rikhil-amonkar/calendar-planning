def main():
    # Convert time string to minutes from 9:00
    def time_str_to_minutes(time_str):
        h, m = time_str.split(':')
        return (int(h) - 9) * 60 + int(m)
    
    # Collect all busy intervals in minutes (from 9:00 as 0 to 17:00 as 480)
    busy_intervals = []
    
    # Doris
    busy_intervals.append((time_str_to_minutes("9:00"), time_str_to_minutes("11:00")))
    busy_intervals.append((time_str_to_minutes("13:30"), time_str_to_minutes("14:00")))
    busy_intervals.append((time_str_to_minutes("16:00"), time_str_to_minutes("16:30")))
    
    # Theresa
    busy_intervals.append((time_str_to_minutes("10:00"), time_str_to_minutes("12:00")))
    
    # Terry
    busy_intervals.append((time_str_to_minutes("9:30"), time_str_to_minutes("10:00")))
    busy_intervals.append((time_str_to_minutes("11:30"), time_str_to_minutes("12:00")))
    busy_intervals.append((time_str_to_minutes("12:30"), time_str_to_minutes("13:00")))
    busy_intervals.append((time_str_to_minutes("13:30"), time_str_to_minutes("14:00")))
    busy_intervals.append((time_str_to_minutes("14:30"), time_str_to_minutes("15:00")))
    busy_intervals.append((time_str_to_minutes("15:30"), time_str_to_minutes("17:00")))
    
    # Carolyn
    busy_intervals.append((time_str_to_minutes("9:00"), time_str_to_minutes("10:30")))
    busy_intervals.append((time_str_to_minutes("11:00"), time_str_to_minutes("11:30")))
    busy_intervals.append((time_str_to_minutes("12:00"), time_str_to_minutes("13:00")))
    busy_intervals.append((time_str_to_minutes("13:30"), time_str_to_minutes("14:30")))
    busy_intervals.append((time_str_to_minutes("15:00"), time_str_to_minutes("17:00")))
    
    # Kyle
    busy_intervals.append((time_str_to_minutes("9:00"), time_str_to_minutes("9:30")))
    busy_intervals.append((time_str_to_minutes("11:30"), time_str_to_minutes("12:00")))
    busy_intervals.append((time_str_to_minutes("12:30"), time_str_to_minutes("13:00")))
    busy_intervals.append((time_str_to_minutes("14:30"), time_str_to_minutes("17:00")))
    
    # Sort busy intervals by start time
    busy_intervals.sort(key=lambda x: x[0])
    
    # Merge overlapping or adjacent intervals
    merged_busy = []
    if busy_intervals:
        current_start, current_end = busy_intervals[0]
        for s, e in busy_intervals[1:]:
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged_busy.append((current_start, current_end))
                current_start, current_end = s, e
        merged_busy.append((current_start, current_end))
    
    # Find free intervals within 9:00 (0 min) to 17:00 (480 min)
    free_intervals = []
    # Before first busy interval
    if not merged_busy:
        free_intervals.append((0, 480))
    else:
        first_start = merged_busy[0][0]
        if first_start > 0:
            free_intervals.append((0, first_start))
        
        # Between busy intervals
        for i in range(len(merged_busy) - 1):
            current_end = merged_busy[i][1]
            next_start = merged_busy[i+1][0]
            if next_start > current_end:
                free_intervals.append((current_end, next_start))
        
        # After last busy interval
        last_end = merged_busy[-1][1]
        if last_end < 480:
            free_intervals.append((last_end, 480))
    
    # Find first free interval of at least 30 minutes
    meeting_start = None
    for start, end in free_intervals:
        if end - start >= 30:
            meeting_start = start
            break
    
    # Convert meeting start and end (30 min later) to time strings
    total_minutes = meeting_start
    hours = total_minutes // 60
    minutes = total_minutes % 60
    start_hour = 9 + hours
    start_minute = minutes
    
    total_minutes_end = meeting_start + 30
    hours_end = total_minutes_end // 60
    minutes_end = total_minutes_end % 60
    end_hour = 9 + hours_end
    end_minute = minutes_end
    
    # Format as HH:MM:HH:MM
    print(f"Monday {start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}")

if __name__ == "__main__":
    main()