def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    day = "Monday"
    work_start_min = time_to_minutes("9:00")
    work_end_min = time_to_minutes("17:00")
    meeting_duration = 30
    
    busy_intervals = []
    
    # Michael's meetings
    busy_intervals.append((time_to_minutes("9:30"), time_to_minutes("10:30")))
    busy_intervals.append((time_to_minutes("15:00"), time_to_minutes("15:30")))
    busy_intervals.append((time_to_minutes("16:00"), time_to_minutes("16:30")))
    
    # Arthur's meetings
    busy_intervals.append((time_to_minutes("9:00"), time_to_minutes("12:00")))
    busy_intervals.append((time_to_minutes("13:00"), time_to_minutes("15:00")))
    busy_intervals.append((time_to_minutes("15:30"), time_to_minutes("16:00")))
    busy_intervals.append((time_to_minutes("16:30"), time_to_minutes("17:00")))
    
    # Eric has no meetings
    
    if not busy_intervals:
        # If no busy intervals, the entire day is free
        start_meeting = work_start_min
        end_meeting = start_meeting + meeting_duration
        start_str = minutes_to_time(start_meeting)
        end_str = minutes_to_time(end_meeting)
        time_range_str = f"{start_str}:{end_str}"
        print(day)
        print(time_range_str)
        return
    
    # Sort the busy intervals by start time
    busy_intervals.sort(key=lambda x: x[0])
    
    # Merge overlapping or adjacent intervals
    merged_busy = []
    current_start, current_end = busy_intervals[0]
    for interval in busy_intervals[1:]:
        s, e = interval
        if s <= current_end:
            current_end = max(current_end, e)
        else:
            merged_busy.append((current_start, current_end))
            current_start, current_end = s, e
    merged_busy.append((current_start, current_end))
    
    # Find free intervals within work hours
    free_intervals = []
    current = work_start_min
    for interval in merged_busy:
        s, e = interval
        if s > current:
            free_intervals.append((current, s))
        current = max(current, e)
    if current < work_end_min:
        free_intervals.append((current, work_end_min))
    
    # Find the first free interval that can fit the meeting
    meeting_start = None
    for s, e in free_intervals:
        if e - s >= meeting_duration:
            meeting_start = s
            break
    
    if meeting_start is None:
        # According to the problem, there exists a solution, so this should not happen.
        print("No suitable time found")
    else:
        meeting_end = meeting_start + meeting_duration
        start_str = minutes_to_time(meeting_start)
        end_str = minutes_to_time(meeting_end)
        time_range_str = f"{start_str}:{end_str}"
        print(day)
        print(time_range_str)

if __name__ == "__main__":
    main()