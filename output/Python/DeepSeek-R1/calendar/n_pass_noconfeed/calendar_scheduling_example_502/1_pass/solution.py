def get_free_intervals(busy_list, work_start, work_end):
    busy_list.sort(key=lambda x: x[0])
    free = []
    current = work_start
    for s, e in busy_list:
        if s >= work_end:
            continue
        if current < s:
            free.append((current, s))
        current = max(current, e + 1)
        if current >= work_end:
            break
    if current < work_end:
        free.append((current, work_end))
    return free

def main():
    # Work hours and constraint: 9:00 to 17:00, but Jack avoids after 12:30
    work_start = 9 * 60  # 9:00 in minutes
    constraint_end = 12 * 60 + 30  # 12:30 in minutes
    work_end = constraint_end  # scheduling only until 12:30

    # Busy intervals (inclusive)
    jack_busy = [
        (9 * 60 + 30, 10 * 60 + 30),  # 9:30-10:30
        (11 * 60, 11 * 60 + 30),      # 11:00-11:30
        (12 * 60 + 30, 13 * 60)       # 12:30-13:00 (starts at constraint_end, skip)
    ]
    charlotte_busy = [
        (9 * 60 + 30, 10 * 60),       # 9:30-10:00
        (10 * 60 + 30, 12 * 60),      # 10:30-12:00
        (12 * 60 + 30, 13 * 60 + 30)  # 12:30-13:30 (skip)
    ]
    
    # Filter out intervals starting at or after work_end
    jack_busy = [(s, e) for s, e in jack_busy if s < work_end]
    charlotte_busy = [(s, e) for s, e in charlotte_busy if s < work_end]
    
    # Compute free intervals
    free_jack = get_free_intervals(jack_busy, work_start, work_end)
    free_charlotte = get_free_intervals(charlotte_busy, work_start, work_end)
    
    # Find the earliest overlapping free interval of at least 30 minutes
    candidate = None
    for j_start, j_end in free_jack:
        for c_start, c_end in free_charlotte:
            start_overlap = max(j_start, c_start)
            end_overlap = min(j_end, c_end)
            if end_overlap - start_overlap >= 30:
                meeting_start = start_overlap
                meeting_end = meeting_start + 30
                candidate = (meeting_start, meeting_end)
                break
        if candidate is not None:
            break
    
    # Format and output the result
    if candidate is None:
        print("No suitable time found")
    else:
        def format_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"
        
        start_str = format_time(candidate[0])
        end_str = format_time(candidate[1])
        print("Monday")
        print(f"{start_str}:{end_str}")

if __name__ == "__main__":
    main()