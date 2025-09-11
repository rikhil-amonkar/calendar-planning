def main():
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    
    # Busy intervals for Nicole and Ruth for each day [start, end) in minutes
    nicole_busy = {
        'Monday': [(540, 570), (780, 810), (870, 930)],
        'Tuesday': [(540, 570), (690, 810), (870, 930)],
        'Wednesday': [(600, 660), (750, 900), (960, 1020)]
    }
    
    ruth_busy = {
        'Monday': [(540, 1020)],
        'Tuesday': [(540, 1020)],
        'Wednesday': [(540, 630), (660, 690), (720, 750), (810, 930), (960, 990)]
    }
    
    # Ruth's constraint: meeting must end by 13:30 (810 minutes) on Wednesday
    wednesday_constraint = 810
    
    def get_free_intervals(busy_list, start, end):
        busy_list.sort(key=lambda x: x[0])
        free_intervals = []
        current = start
        for bus_start, bus_end in busy_list:
            if bus_start > current:
                free_intervals.append((current, bus_start))
            current = max(current, bus_end)
        if current < end:
            free_intervals.append((current, end))
        return free_intervals
    
    def find_common_intervals(intervals1, intervals2):
        common = []
        i = j = 0
        while i < len(intervals1) and j < len(intervals2):
            s1, e1 = intervals1[i]
            s2, e2 = intervals2[j]
            low = max(s1, s2)
            high = min(e1, e2)
            if low < high:
                common.append((low, high))
            if e1 < e2:
                i += 1
            else:
                j += 1
        return common
    
    for day in days:
        nicole_free = get_free_intervals(nicole_busy[day], work_start, work_end)
        ruth_free = get_free_intervals(ruth_busy[day], work_start, work_end)
        common_free = find_common_intervals(nicole_free, ruth_free)
        
        for s, e in common_free:
            if day == 'Wednesday':
                max_end = min(e, wednesday_constraint)
            else:
                max_end = e
            if s + meeting_duration <= max_end:
                start_str = f"{s // 60:02d}:{s % 60:02d}"
                end_str = f"{(s + meeting_duration) // 60:02d}:{(s + meeting_duration) % 60:02d}"
                print(f"{day} {start_str}:{end_str}")
                return
    
    print("No suitable time found.")

if __name__ == "__main__":
    main()