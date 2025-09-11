def main():
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    meeting_duration = 30
    day = "Monday"
    
    # Busy intervals in minutes
    emily_busy = [
        (10*60, 10*60+30),   # 10:00-10:30
        (11*60+30, 12*60+30), # 11:30-12:30
        (14*60, 15*60),       # 14:00-15:00
        (16*60, 16*60+30)     # 16:00-16:30
    ]
    
    melissa_busy = [
        (9*60+30, 10*60),    # 9:30-10:00
        (14*60+30, 15*60)    # 14:30-15:00
    ]
    
    frank_busy = [
        (10*60, 10*60+30),   # 10:00-10:30
        (11*60, 11*60+30),   # 11:00-11:30
        (12*60+30, 13*60),   # 12:30-13:00
        (13*60+30, 14*60+30),# 13:30-14:30
        (15*60, 16*60),      # 15:00-16:00
        (16*60+30, 17*60)    # 16:30-17:00
    ]
    
    # Function to calculate free intervals
    def get_free_intervals(busy, start, end):
        free = []
        current = start
        for busy_start, busy_end in sorted(busy):
            if current < busy_start:
                free.append((current, busy_start))
            current = max(current, busy_end)
        if current < end:
            free.append((current, end))
        return free
    
    emily_free = get_free_intervals(emily_busy, work_start, work_end)
    melissa_free = get_free_intervals(melissa_busy, work_start, work_end)
    frank_free = get_free_intervals(frank_busy, work_start, work_end)
    
    # Function to intersect two sets of intervals
    def intersect_intervals(intervals1, intervals2):
        i = j = 0
        result = []
        while i < len(intervals1) and j < len(intervals2):
            a_start, a_end = intervals1[i]
            b_start, b_end = intervals2[j]
            start = max(a_start, b_start)
            end = min(a_end, b_end)
            if start < end:
                result.append((start, end))
            if a_end < b_end:
                i += 1
            else:
                j += 1
        return result
    
    common_free = intersect_intervals(emily_free, melissa_free)
    common_free = intersect_intervals(common_free, frank_free)
    
    # Find a meeting slot that ends by 9:30 (570 minutes)
    meeting_time = None
    for slot_start, slot_end in common_free:
        # Check if the slot can accommodate the meeting and ends by 9:30
        if slot_end >= slot_start + meeting_duration and slot_start + meeting_duration <= 570:
            meeting_time = (slot_start, slot_start + meeting_duration)
            break
    
    if meeting_time:
        start_min, end_min = meeting_time
        # Convert minutes to HH:MM format
        start_str = f"{start_min//60:02d}:{start_min%60:02d}"
        end_str = f"{end_min//60:02d}:{end_min%60:02d}"
        print(f"{day} {start_str}:{end_str}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()