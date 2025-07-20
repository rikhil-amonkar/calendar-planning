def main():
    work_start = 9 * 60  # 540 minutes (9:00)
    work_end = 17 * 60    # 1020 minutes (17:00)
    duration = 30         # Meeting duration in minutes

    # List all busy intervals in minutes since midnight
    busy = []
    
    # Andrea: no meetings
    # Jack
    busy.append((9*60, 9*60+30))       # 9:00-9:30
    busy.append((14*60, 14*60+30))      # 14:00-14:30
    
    # Madison
    busy.append((9*60+30, 10*60+30))   # 9:30-10:30
    busy.append((13*60, 14*60))         # 13:00-14:00
    busy.append((15*60, 15*60+30))      # 15:00-15:30
    busy.append((16*60+30, 17*60))      # 16:30-17:00
    
    # Rachel
    busy.append((9*60+30, 10*60+30))    # 9:30-10:30
    busy.append((11*60, 11*60+30))       # 11:00-11:30
    busy.append((12*60, 13*60+30))       # 12:00-13:30
    busy.append((14*60+30, 15*60+30))    # 14:30-15:30
    busy.append((16*60, 17*60))          # 16:00-17:00
    
    # Douglas
    busy.append((9*60, 11*60+30))        # 9:00-11:30
    busy.append((12*60, 16*60+30))       # 12:00-16:30
    
    # Ryan
    busy.append((9*60, 9*60+30))         # 9:00-9:30
    busy.append((13*60, 14*60))           # 13:00-14:00
    busy.append((14*60+30, 17*60))        # 14:30-17:00

    # Merge overlapping busy intervals
    if not busy:
        merged = []
    else:
        busy.sort()
        merged = [busy[0]]
        for i in range(1, len(busy)):
            current_start, current_end = busy[i]
            last_start, last_end = merged[-1]
            if current_start <= last_end:
                merged[-1] = (last_start, max(last_end, current_end))
            else:
                merged.append(busy[i])
    
    # Find free intervals within work hours
    free_intervals = []
    if merged:
        # Before first meeting
        if work_start < merged[0][0]:
            free_intervals.append((work_start, merged[0][0]))
        
        # Between meetings
        for i in range(1, len(merged)):
            prev_end = merged[i-1][1]
            current_start = merged[i][0]
            if prev_end < current_start:
                free_intervals.append((prev_end, current_start))
        
        # After last meeting
        if merged[-1][1] < work_end:
            free_intervals.append((merged[-1][1], work_end))
    else:
        free_intervals.append((work_start, work_end))
    
    # Find first free interval that can fit the meeting
    meeting_start = None
    for start, end in free_intervals:
        if end - start >= duration:
            meeting_start = start
            meeting_end = start + duration
            break
    
    # Convert meeting time to HH:MM format
    def min_to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"
    
    if meeting_start is not None:
        start_str = min_to_time(meeting_start)
        end_str = min_to_time(meeting_end)
        time_range = f"{start_str}:{end_str}"
        print(f"Monday:{time_range}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()