def main():
    work_start = 0
    work_end = 480
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    
    raymond_busy_all = {
        'Monday': [[0, 30], [150, 180], [240, 270], [360, 390]],
        'Tuesday': [],
        'Wednesday': [],
        'Thursday': [],
        'Friday': []
    }
    
    billy_busy_all = {
        'Monday': [[60, 90], [180, 240], [450, 480]],
        'Tuesday': [],
        'Wednesday': [],
        'Thursday': [],
        'Friday': []
    }
    
    donald_busy_all = {
        'Monday': [[0, 30], [60, 120], [180, 240], [300, 330], [420, 480]],
        'Tuesday': [],
        'Wednesday': [],
        'Thursday': [],
        'Friday': []
    }
    
    def get_free_intervals(busy_intervals, start, end):
        if not busy_intervals:
            return [[start, end]]
        sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
        free = []
        current = start
        for interval in sorted_busy:
            s, e = interval
            if current < s:
                free.append([current, s])
            current = max(current, e)
        if current < end:
            free.append([current, end])
        return free

    def intersect_intervals(intervals1, intervals2):
        if not intervals1 or not intervals2:
            return []
        i, j = 0, 0
        result = []
        while i < len(intervals1) and j < len(intervals2):
            a1, a2 = intervals1[i]
            b1, b2 = intervals2[j]
            start = max(a1, b1)
            end = min(a2, b2)
            if start < end:
                result.append([start, end])
            if a2 < b2:
                i += 1
            else:
                j += 1
        return result

    candidate_slot = None
    candidate_day = None

    for day in days:
        raymond_busy = raymond_busy_all[day]
        billy_busy = billy_busy_all[day]
        donald_busy = donald_busy_all[day]
        
        raymond_free = get_free_intervals(raymond_busy, work_start, work_end)
        billy_free = get_free_intervals(billy_busy, work_start, work_end)
        donald_free = get_free_intervals(donald_busy, work_start, work_end)
        
        common_free = intersect_intervals(raymond_free, billy_free)
        common_free = intersect_intervals(common_free, donald_free)
        
        for interval in common_free:
            start, end = interval
            if start + 30 <= end and start <= 450:
                candidate_slot = [start, start + 30]
                candidate_day = day
                break
        if candidate_slot:
            break
            
    if candidate_slot:
        def minutes_to_time(minutes):
            total_minutes = minutes
            hours = 9 + total_minutes // 60
            mins = total_minutes % 60
            return f"{hours:02d}:{mins:02d}"
        
        start_time = minutes_to_time(candidate_slot[0])
        end_time = minutes_to_time(candidate_slot[1])
        print(f"{start_time}-{end_time}")
        print(candidate_day)
    else:
        print("No meeting available")

if __name__ == "__main__":
    main()