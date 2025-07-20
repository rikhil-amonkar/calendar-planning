def get_free_intervals(work_start, work_end, busy_intervals):
    if not busy_intervals:
        return [(work_start, work_end)]
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current_start = work_start
    for interval in sorted_busy:
        busy_start, busy_end = interval
        if busy_start > current_start:
            free.append((current_start, busy_start))
        current_start = max(current_start, busy_end)
    if current_start < work_end:
        free.append((current_start, work_end))
    return free

def minutes_to_time_str(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def main():
    work_start = 9 * 60
    work_end = 17 * 60
    duration = 30  # minutes

    days = ['Monday', 'Tuesday', 'Wednesday']
    
    tyler_busy = {
        'Tuesday': [(9*60, 9*60+30), (14*60+30, 15*60)],
        'Wednesday': [(10*60+30, 11*60), (12*60+30, 13*60), (13*60+30, 14*60), (16*60+30, 17*60)]
    }
    
    ruth_busy = {
        'Monday': [(9*60, 10*60), (10*60+30, 12*60), (12*60+30, 14*60+30), (15*60, 16*60), (16*60+30, 17*60)],
        'Tuesday': [(9*60, 17*60)],
        'Wednesday': [(9*60, 17*60)]
    }
    
    for day in days:
        tyler_free = get_free_intervals(work_start, work_end, tyler_busy.get(day, []))
        ruth_free = get_free_intervals(work_start, work_end, ruth_busy.get(day, []))
        
        common_free = []
        for t_interval in tyler_free:
            for r_interval in ruth_free:
                start_overlap = max(t_interval[0], r_interval[0])
                end_overlap = min(t_interval[1], r_interval[1])
                if start_overlap < end_overlap:
                    common_free.append((start_overlap, end_overlap))
        
        if day == 'Monday':
            common_free = [interval for interval in common_free if interval[0] >= 16*60]
        
        common_free.sort(key=lambda x: x[0])
        
        for start, end in common_free:
            if end - start >= duration:
                meeting_start = start
                meeting_end = start + duration
                day_str = day
                start_time_str = minutes_to_time_str(meeting_start)
                end_time_str = minutes_to_time_str(meeting_end)
                print(day_str)
                print(f"{start_time_str}:{end_time_str}")
                return
                
    print("No suitable time found")

if __name__ == "__main__":
    main()