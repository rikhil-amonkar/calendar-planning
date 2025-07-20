def main():
    work_start = 9 * 60  # 540 minutes (9:00)
    work_end = 17 * 60   # 1020 minutes (17:00)
    
    # Eric's busy intervals in minutes: (start, end)
    eric_busy = [(12*60, 13*60), (14*60, 15*60)]
    # Henry's busy intervals in minutes: (start, end)
    henry_busy = [(9*60+30, 10*60), (10*60+30, 11*60), (11*60+30, 12*60+30), 
                  (13*60, 13*60+30), (14*60+30, 15*60), (16*60, 17*60)]
    
    # Function to compute free intervals given busy intervals and work hours
    def get_free_intervals(busy_list, work_start, work_end):
        if not busy_list:
            return [(work_start, work_end)]
        sorted_busy = sorted(busy_list, key=lambda x: x[0])
        free_intervals = []
        current_start = work_start
        for start, end in sorted_busy:
            if current_start < start:
                free_intervals.append((current_start, start))
            current_start = end
        if current_start < work_end:
            free_intervals.append((current_start, work_end))
        return free_intervals
    
    eric_free = get_free_intervals(eric_busy, work_start, work_end)
    henry_free = get_free_intervals(henry_busy, work_start, work_end)
    
    # Find common free intervals
    common_free = []
    for e_start, e_end in eric_free:
        for h_start, h_end in henry_free:
            start = max(e_start, h_start)
            end = min(e_end, h_end)
            if start < end:
                common_free.append((start, end))
    
    # Sort common free intervals by start time
    common_free.sort(key=lambda x: x[0])
    
    meeting_start_min = None
    meeting_end_min = None
    preference_end = 10 * 60  # 10:00 in minutes (600)
    
    # Try to find a slot ending by 10:00 (600 minutes)
    for start, end in common_free:
        available_end = min(end, preference_end)
        if available_end - start >= 30:
            meeting_start_min = start
            meeting_end_min = start + 30
            break
    
    # If no slot before 10:00, find the first available 30-minute slot
    if meeting_start_min is None:
        for start, end in common_free:
            if end - start >= 30:
                meeting_start_min = start
                meeting_end_min = start + 30
                break
    
    # Convert meeting times to HH:MM format
    start_hour = meeting_start_min // 60
    start_minute = meeting_start_min % 60
    end_hour = meeting_end_min // 60
    end_minute = meeting_end_min % 60
    
    time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
    
    print("Monday")
    print(time_str)

if __name__ == "__main__":
    main()