def get_free_intervals(blocks, work_start, work_end):
    if not blocks:
        return [(work_start, work_end)]
    sorted_blocks = sorted(blocks, key=lambda x: x[0])
    merged = []
    start_curr, end_curr = sorted_blocks[0]
    for i in range(1, len(sorted_blocks)):
        s, e = sorted_blocks[i]
        if s <= end_curr:
            end_curr = max(end_curr, e)
        else:
            merged.append((start_curr, end_curr))
            start_curr, end_curr = s, e
    merged.append((start_curr, end_curr))
    
    free = []
    current = work_start
    for s, e in merged:
        if current < s:
            free.append((current, s))
        current = max(current, e)
    if current < work_end:
        free.append((current, work_end))
    return free

def format_time_range(start_min, end_min):
    start_h = start_min // 60
    start_m = start_min % 60
    end_h = end_min // 60
    end_m = end_min % 60
    return f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"

def main():
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    duration = 60        # 60 minutes

    # Define blocked times for each participant by day
    judith_blocks = {
        'Monday': [(12*60, 12*60+30)],       # 12:00-12:30
        'Wednesday': [(11*60+30, 12*60)],     # 11:30-12:00
    }
    
    timothy_blocks = {
        'Monday': [
            (9*60+30, 10*60),        # 9:30-10:00
            (10*60+30, 11*60+30),     # 10:30-11:30
            (12*60+30, 14*60),        # 12:30-14:00
            (15*60+30, 17*60)         # 15:30-17:00
        ],
        'Tuesday': [
            (9*60+30, 13*60),        # 9:30-13:00
            (13*60+30, 14*60),        # 13:30-14:00
            (14*60+30, 17*60)         # 14:30-17:00
        ],
        'Wednesday': [
            (9*60, 9*60+30),          # 9:00-9:30
            (10*60+30, 11*60),        # 10:30-11:00
            (13*60+30, 14*60+30),     # 13:30-14:30
            (15*60, 15*60+30),        # 15:00-15:30
            (16*60, 16*60+30)         # 16:00-16:30
        ]
    }
    
    days_order = ['Tuesday', 'Wednesday', 'Monday']  # Preference order
    
    for day in days_order:
        # Get blocks for Judith and Timothy for this day
        j_blocks = judith_blocks.get(day, [])
        t_blocks = timothy_blocks.get(day, [])
        
        # Compute free intervals
        free_j = get_free_intervals(j_blocks, work_start, work_end)
        free_t = get_free_intervals(t_blocks, work_start, work_end)
        
        # For Wednesday, filter Judith's free intervals to after 12:00
        if day == 'Wednesday':
            free_j = [(s, e) for s, e in free_j if s >= 12*60]  # 12:00 in minutes
        
        # Find overlapping free intervals with sufficient duration
        for j_start, j_end in free_j:
            for t_start, t_end in free_t:
                start_overlap = max(j_start, t_start)
                end_overlap = min(j_end, t_end)
                if end_overlap - start_overlap >= duration:
                    meeting_start = start_overlap
                    meeting_end = meeting_start + duration
                    time_str = format_time_range(meeting_start, meeting_end)
                    print(day)
                    print(time_str)
                    return
    
    # If no slot found (though problem states there is a solution)
    print("No suitable time found")

if __name__ == "__main__":
    main()