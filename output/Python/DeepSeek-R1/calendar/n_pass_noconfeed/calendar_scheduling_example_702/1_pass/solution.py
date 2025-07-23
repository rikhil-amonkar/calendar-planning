def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return hours * 60 + minutes

def minutes_to_time(minutes_val):
    hours = minutes_val // 60
    minutes = minutes_val % 60
    return f"{hours:02d}:{minutes:02d}"

robert_busy = {
    "Monday": [("11:00", "11:30"), ("14:00", "14:30"), ("15:30", "16:00")],
    "Tuesday": [("10:30", "11:00"), ("15:00", "15:30")],
    "Wednesday": [("10:00", "11:00"), ("11:30", "12:00"), ("12:30", "13:00"), ("13:30", "14:00"), ("15:00", "15:30"), ("16:00", "16:30")]
}

ralph_busy = {
    "Monday": [("10:00", "13:30"), ("14:00", "14:30"), ("15:00", "17:00")],
    "Tuesday": [("9:00", "9:30"), ("10:00", "10:30"), ("11:00", "11:30"), ("12:00", "13:00"), ("14:00", "15:30"), ("16:00", "17:00")],
    "Wednesday": [("10:30", "11:00"), ("11:30", "12:00"), ("13:00", "14:30"), ("16:30", "17:00")]
}

work_start = time_to_minutes("9:00")
work_end = time_to_minutes("17:00")

days_order = ["Tuesday", "Wednesday", "Monday"]

found_slot = False
for day in days_order:
    busy_list = []
    if day in robert_busy:
        for interval in robert_busy[day]:
            s = time_to_minutes(interval[0])
            e = time_to_minutes(interval[1])
            busy_list.append((s, e))
    if day in ralph_busy:
        for interval in ralph_busy[day]:
            s = time_to_minutes(interval[0])
            e = time_to_minutes(interval[1])
            busy_list.append((s, e))
            
    if not busy_list:
        free_intervals = [(work_start, work_end)]
    else:
        busy_list.sort(key=lambda x: x[0])
        merged_busy = []
        current_start, current_end = busy_list[0]
        for i in range(1, len(busy_list)):
            s, e = busy_list[i]
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged_busy.append((current_start, current_end))
                current_start, current_end = s, e
        merged_busy.append((current_start, current_end))
        
        free_intervals = []
        current = work_start
        for interval in merged_busy:
            s, e = interval
            if current < s:
                free_intervals.append((current, s))
            current = max(current, e)
        if current < work_end:
            free_intervals.append((current, work_end))
    
    for interval in free_intervals:
        start_free, end_free = interval
        duration = end_free - start_free
        if duration >= 30:
            meeting_start = start_free
            meeting_end = start_free + 30
            start_hour = meeting_start // 60
            start_minute = meeting_start % 60
            end_hour = meeting_end // 60
            end_minute = meeting_end % 60
            time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
            print(day)
            print(time_str)
            found_slot = True
            break
    if found_slot:
        break