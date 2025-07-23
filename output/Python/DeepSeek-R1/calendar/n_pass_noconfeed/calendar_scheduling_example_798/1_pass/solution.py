def compute_free(work_start, work_end, busy_list):
    if not busy_list:
        return [(work_start, work_end)]
    sorted_busy = sorted(busy_list, key=lambda x: x[0])
    free = []
    current = work_start
    for busy_start, busy_end in sorted_busy:
        if current < busy_start:
            free.append((current, busy_start))
        current = max(current, busy_end)
    if current < work_end:
        free.append((current, work_end))
    return free

def compute_common_free(free1, free2):
    i = j = 0
    common = []
    while i < len(free1) and j < len(free2):
        low = max(free1[i][0], free2[j][0])
        high = min(free1[i][1], free2[j][1])
        if low < high:
            common.append((low, high))
        if free1[i][1] < free2[j][1]:
            i += 1
        else:
            j += 1
    return common

def main():
    work_start_min = 9 * 60
    work_end_min = 17 * 60
    days = ['Monday', 'Tuesday', 'Wednesday']
    
    nancy_busy = {
        'Monday': [(10*60, 10*60+30), (11*60+30, 12*60+30), (13*60+30, 14*60), (14*60+30, 15*60+30), (16*60, 17*60)],
        'Tuesday': [(9*60+30, 10*60+30), (11*60, 11*60+30), (12*60, 12*60+30), (13*60, 13*60+30), (15*60+30, 16*60)],
        'Wednesday': [(10*60, 11*60+30), (13*60+30, 16*60)]
    }
    
    jose_busy = {
        'Monday': [(9*60, 17*60)],
        'Tuesday': [(9*60, 17*60)],
        'Wednesday': [(9*60, 9*60+30), (10*60, 12*60+30), (13*60+30, 14*60+30), (15*60, 17*60)]
    }
    
    for day in days:
        free_nancy = compute_free(work_start_min, work_end_min, nancy_busy[day])
        free_jose = compute_free(work_start_min, work_end_min, jose_busy[day])
        common_free = compute_common_free(free_nancy, free_jose)
        
        for start, end in common_free:
            duration = end - start
            if duration >= 30:
                meeting_start = start
                meeting_end = start + 30
                start_h = meeting_start // 60
                start_m = meeting_start % 60
                end_h = meeting_end // 60
                end_m = meeting_end % 60
                time_str = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
                print(day)
                print(time_str)
                return
    print("No suitable time found")

if __name__ == "__main__":
    main()