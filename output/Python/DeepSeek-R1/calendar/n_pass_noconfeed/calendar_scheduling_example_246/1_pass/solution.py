def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def main():
    work_start_min = 9 * 60  # 9:00
    work_end_min = 17 * 60   # 17:00
    meeting_duration = 30
    
    # Collect all busy intervals in minutes
    all_busy = []
    
    # Jacob
    all_busy.append((time_to_minutes("13:30"), time_to_minutes("14:00")))
    all_busy.append((time_to_minutes("14:30"), time_to_minutes("15:00")))
    
    # Diana
    all_busy.append((time_to_minutes("9:30"), time_to_minutes("10:00")))
    all_busy.append((time_to_minutes("11:30"), time_to_minutes("12:00")))
    all_busy.append((time_to_minutes("13:00"), time_to_minutes("13:30")))
    all_busy.append((time_to_minutes("16:00"), time_to_minutes("16:30")))
    
    # Adam
    all_busy.append((time_to_minutes("9:30"), time_to_minutes("10:30")))
    all_busy.append((time_to_minutes("11:00"), time_to_minutes("12:30")))
    all_busy.append((time_to_minutes("15:30"), time_to_minutes("16:00")))
    
    # Angela
    all_busy.append((time_to_minutes("9:30"), time_to_minutes("10:00")))
    all_busy.append((time_to_minutes("10:30"), time_to_minutes("12:00")))
    all_busy.append((time_to_minutes("13:00"), time_to_minutes("15:30")))
    all_busy.append((time_to_minutes("16:00"), time_to_minutes("16:30")))
    
    # Dennis
    all_busy.append((time_to_minutes("9:00"), time_to_minutes("9:30")))
    all_busy.append((time_to_minutes("10:30"), time_to_minutes("11:30")))
    all_busy.append((time_to_minutes("13:00"), time_to_minutes("15:00")))
    all_busy.append((time_to_minutes("16:30"), time_to_minutes("17:00")))
    
    # Sort by start time
    all_busy.sort(key=lambda x: x[0])
    
    # Merge overlapping or adjacent intervals
    merged_busy = []
    for interval in all_busy:
        if not merged_busy:
            merged_busy.append(interval)
        else:
            last_start, last_end = merged_busy[-1]
            current_start, current_end = interval
            if current_start <= last_end:
                merged_busy[-1] = (last_start, max(last_end, current_end))
            else:
                merged_busy.append(interval)
    
    # Find free intervals
    free_intervals = []
    current_start = work_start_min
    
    for start, end in merged_busy:
        if current_start < start:
            free_intervals.append((current_start, start))
        current_start = end
    if current_start < work_end_min:
        free_intervals.append((current_start, work_end_min))
    
    # Find the first free interval that fits the meeting
    meeting_start_min = None
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_start_min = start
            break
    
    if meeting_start_min is None:
        print("No suitable time found")
        return
    
    meeting_end_min = meeting_start_min + meeting_duration
    
    # Convert meeting start and end to HH:MM components
    start_hr = meeting_start_min // 60
    start_min = meeting_start_min % 60
    end_hr = meeting_end_min // 60
    end_min = meeting_end_min % 60
    
    # Format the output
    time_str = f"{start_hr:02d}:{start_min:02d}:{end_hr:02d}:{end_min:02d}"
    print("Monday")
    print(time_str)

if __name__ == "__main__":
    main()