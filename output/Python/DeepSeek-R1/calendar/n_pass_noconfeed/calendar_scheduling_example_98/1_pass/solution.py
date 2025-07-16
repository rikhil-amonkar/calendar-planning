def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    total_minutes = (hours - 9) * 60 + minutes
    return total_minutes

def minutes_to_time(minutes_val):
    total_minutes = minutes_val
    hours = 9 + total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def main():
    day = "Monday"
    meeting_duration = 30
    day_end_minutes = time_to_minutes("16:00")  # Meeting must end by 16:00

    # Busy intervals for Juan
    juan_intervals = [
        ("9:00", "10:30"),
        ("15:30", "16:00")
    ]
    # Busy intervals for Marilyn
    marilyn_intervals = [
        ("11:00", "11:30"),
        ("12:30", "13:00")
    ]
    # Busy intervals for Ronald
    ronald_intervals = [
        ("9:00", "10:30"),
        ("12:00", "12:30"),
        ("13:00", "13:30"),
        ("14:00", "16:30")  # Will be clipped to 16:00
    ]
    
    all_busy = []
    
    for start_str, end_str in juan_intervals:
        start_min = time_to_minutes(start_str)
        end_min = time_to_minutes(end_str)
        if start_min < day_end_minutes:  # Only consider intervals within the effective day
            end_min = min(end_min, day_end_minutes)
            if end_min > start_min:
                all_busy.append((start_min, end_min))
    
    for start_str, end_str in marilyn_intervals:
        start_min = time_to_minutes(start_str)
        end_min = time_to_minutes(end_str)
        if start_min < day_end_minutes:
            end_min = min(end_min, day_end_minutes)
            if end_min > start_min:
                all_busy.append((start_min, end_min))
    
    for start_str, end_str in ronald_intervals:
        start_min = time_to_minutes(start_str)
        end_min = time_to_minutes(end_str)
        if start_min < day_end_minutes:
            end_min = min(end_min, day_end_minutes)
            if end_min > start_min:
                all_busy.append((start_min, end_min))
    
    if not all_busy:
        merged = []
    else:
        all_busy.sort(key=lambda x: x[0])
        merged = []
        current_start, current_end = all_busy[0]
        for interval in all_busy[1:]:
            if interval[0] <= current_end:
                current_end = max(current_end, interval[1])
            else:
                merged.append((current_start, current_end))
                current_start, current_end = interval
        merged.append((current_start, current_end))
    
    current_time = 0
    slot_found = False
    slot_start_min = None
    slot_end_min = None
    
    for start, end in merged:
        if start - current_time >= meeting_duration:
            slot_start_min = current_time
            slot_end_min = current_time + meeting_duration
            slot_found = True
            break
        current_time = max(current_time, end)
    
    if not slot_found:
        if day_end_minutes - current_time >= meeting_duration:
            slot_start_min = current_time
            slot_end_min = current_time + meeting_duration
            slot_found = True
    
    if slot_found:
        start_time_str = minutes_to_time(slot_start_min)
        end_time_str = minutes_to_time(slot_end_min)
        time_range_str = f"{start_time_str}:{end_time_str}"
        print(day)
        print(time_range_str)
    else:
        print("No suitable slot found")

if __name__ == "__main__":
    main()