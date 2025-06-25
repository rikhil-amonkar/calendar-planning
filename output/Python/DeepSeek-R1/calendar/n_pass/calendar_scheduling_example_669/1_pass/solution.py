def main():
    work_start = 540  # 9:00 in minutes
    work_end = 1020   # 17:00 in minutes
    days = ['Monday', 'Tuesday']
    
    # Busy intervals for Jean and Doris for each day (in minutes, [start, end))
    jean_busy = {
        'Monday': [],
        'Tuesday': [[690, 720], [960, 990]]  # 11:30-12:00, 16:00-16:30
    }
    
    doris_busy = {
        'Monday': [[540, 690], [720, 750], [810, 960], [990, 1020]],  # 9:00-11:30, 12:00-12:30, 13:30-16:00, 16:30-17:00
        'Tuesday': [[540, 1020]]  # Entire work day busy
    }
    
    # Helper function to compute free intervals
    def compute_free(work_start, work_end, busy_intervals):
        if not busy_intervals:
            return [[work_start, work_end]]
        sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
        free = []
        current = work_start
        for s, e in sorted_busy:
            if s > current:
                free.append([current, s])
            if e > current:
                current = e
        if current < work_end:
            free.append([current, work_end])
        return free
    
    # Helper function to find intersection of two sets of intervals
    def intersect_intervals(intervals1, intervals2):
        i = j = 0
        common = []
        while i < len(intervals1) and j < len(intervals2):
            low = max(intervals1[i][0], intervals2[j][0])
            high = min(intervals1[i][1], intervals2[j][1])
            if low < high:
                common.append([low, high])
            if intervals1[i][1] < intervals2[j][1]:
                i += 1
            else:
                j += 1
        return common
    
    # Helper function to convert minutes to HH:MM string
    def format_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"
    
    # Iterate over days to find a suitable meeting time
    chosen_day = None
    chosen_interval = None
    
    for day in days:
        jean_free = compute_free(work_start, work_end, jean_busy[day])
        doris_free = compute_free(work_start, work_end, doris_busy[day])
        common = intersect_intervals(jean_free, doris_free)
        # Filter intervals with at least 30 minutes duration
        common = [interv for interv in common if interv[1] - interv[0] >= 30]
        
        if not common:
            continue
            
        if day == 'Monday':
            # Filter intervals starting before 14:00 (840 minutes) for Doris's preference
            preferred_common = [interv for interv in common if interv[0] < 840]
            if preferred_common:
                chosen_interval = preferred_common[0]
                chosen_day = day
                break
            else:
                chosen_interval = common[0]
                chosen_day = day
                break
        else:
            chosen_interval = common[0]
            chosen_day = day
            break
    
    if chosen_interval:
        start_time = format_time(chosen_interval[0])
        end_time = format_time(chosen_interval[1])
        time_str = f"{start_time}:{end_time}"
        print(chosen_day)
        print(time_str)

if __name__ == "__main__":
    main()