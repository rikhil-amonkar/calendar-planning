def main():
    work_start = 9 * 60  # 9:00 in minutes (540)
    work_end = 17 * 60    # 17:00 in minutes (1020)
    meeting_duration = 60  # 60 minutes

    # List to collect all busy intervals (each as [start, end) in minutes)
    busy_intervals = []
    
    # Joshua's busy intervals
    busy_intervals.append([11*60, 12*60+30])    # 11:00-12:30
    busy_intervals.append([13*60+30, 14*60+30]) # 13:30-14:30
    busy_intervals.append([16*60+30, 17*60])    # 16:30-17:00
    
    # Jerry's busy intervals
    busy_intervals.append([9*60, 9*60+30])       # 9:00-9:30
    busy_intervals.append([10*60+30, 12*60])     # 10:30-12:00
    busy_intervals.append([12*60+30, 13*60])     # 12:30-13:00
    busy_intervals.append([13*60+30, 14*60])     # 13:30-14:00
    busy_intervals.append([14*60+30, 15*60])     # 14:30-15:00
    busy_intervals.append([15*60+30, 16*60])     # 15:30-16:00
    
    # Jesse's busy intervals
    busy_intervals.append([9*60, 9*60+30])       # 9:00-9:30
    busy_intervals.append([10*60+30, 12*60])     # 10:30-12:00
    busy_intervals.append([12*60+30, 13*60])     # 12:30-13:00
    busy_intervals.append([14*60+30, 15*60])     # 14:30-15:00
    busy_intervals.append([15*60+30, 16*60+30])  # 15:30-16:30
    
    # Kenneth's busy intervals
    busy_intervals.append([10*60+30, 12*60+30])  # 10:30-12:30
    busy_intervals.append([13*60+30, 14*60])     # 13:30-14:00
    busy_intervals.append([14*60+30, 15*60])     # 14:30-15:00
    busy_intervals.append([15*60+30, 16*60])     # 15:30-16:00
    busy_intervals.append([16*60+30, 17*60])     # 16:30-17:00
    
    # Merge busy intervals
    if not busy_intervals:
        merged_busy = []
    else:
        busy_intervals.sort(key=lambda x: x[0])
        merged_busy = []
        start, end = busy_intervals[0]
        for interval in busy_intervals[1:]:
            if interval[0] <= end:
                end = max(end, interval[1])
            else:
                merged_busy.append([start, end])
                start, end = interval
        merged_busy.append([start, end])
    
    # Find free intervals within work hours
    free_intervals = []
    current = work_start
    for busy in merged_busy:
        if busy[0] > current:
            free_intervals.append([current, busy[0]])
        current = max(current, busy[1])
    if current < work_end:
        free_intervals.append([current, work_end])
    
    # Find the first free interval that can fit the meeting
    meeting_slot = None
    for interval in free_intervals:
        start, end = interval
        duration = end - start
        if duration >= meeting_duration:
            meeting_slot = [start, start + meeting_duration]
            break
    
    # Format the output
    if meeting_slot:
        start_minutes = meeting_slot[0]
        end_minutes = meeting_slot[1]
        start_hour = start_minutes // 60
        start_min = start_minutes % 60
        end_hour = end_minutes // 60
        end_min = end_minutes % 60
        print(f"Monday {start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}")
    else:
        print("No suitable slot found")

if __name__ == "__main__":
    main()