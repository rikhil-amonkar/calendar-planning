def compute_free_intervals(busy_intervals, work_start, work_end):
    if not busy_intervals:
        return [(work_start, work_end)]
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current = work_start
    for s, e in sorted_busy:
        s_clip = max(s, work_start)
        e_clip = min(e, work_end)
        if s_clip >= e_clip:
            continue
        if current < s_clip:
            free.append((current, s_clip))
        current = max(current, e_clip)
    if current < work_end:
        free.append((current, work_end))
    return free

def find_common_slots(free1, free2):
    common = []
    i = j = 0
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
    stephanie_busy = {
        'Monday': [(570, 600), (630, 660), (690, 720), (840, 870)],
        'Tuesday': [(720, 780)],
        'Wednesday': [(540, 600), (780, 840)],
    }
    
    betty_busy = {
        'Monday': [(540, 600), (660, 690), (870, 900), (930, 960)],
        'Tuesday': [(540, 570), (690, 720)],
        'Wednesday': [(600, 690), (720, 840), (870, 1020)],
    }
    
    days_order = ['Tuesday', 'Wednesday', 'Monday']
    work_start_min = 9 * 60  # 9:00
    
    for day in days_order:
        if day == 'Tuesday':
            work_end_min = 12 * 60 + 30  # 12:30
        else:
            work_end_min = 17 * 60  # 17:00
        
        s_busy = stephanie_busy.get(day, [])
        b_busy = betty_busy.get(day, [])
        
        s_free = compute_free_intervals(s_busy, work_start_min, work_end_min)
        b_free = compute_free_intervals(b_busy, work_start_min, work_end_min)
        common_free = find_common_slots(s_free, b_free)
        
        for start, end in common_free:
            if end - start >= 60:
                slot_start = start
                slot_end = start + 60
                start_hr, start_min = divmod(slot_start, 60)
                end_hr, end_min = divmod(slot_end, 60)
                time_str = f"{start_hr:02d}:{start_min:02d}:{end_hr:02d}:{end_min:02d}"
                print(day)
                print(time_str)
                return

if __name__ == "__main__":
    main()