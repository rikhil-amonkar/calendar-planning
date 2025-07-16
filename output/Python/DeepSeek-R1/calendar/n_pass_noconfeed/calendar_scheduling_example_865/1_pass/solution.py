def get_free_slots(busy_list, work_start, work_end):
    if not busy_list:
        return [(work_start, work_end)]
    busy_list.sort(key=lambda x: x[0])
    free_slots = []
    current = work_start
    for start, end in busy_list:
        if current < start:
            free_slots.append((current, start))
        current = max(current, end)
    if current < work_end:
        free_slots.append((current, work_end))
    return free_slots

def main():
    work_start = 540  # 9:00 in minutes
    work_end = 1020   # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    
    megan_busy = {
        'Monday': [(13*60, 13*60+30), (14*60, 15*60+30)],
        'Tuesday': [(9*60, 9*60+30), (12*60, 12*60+30), (16*60, 17*60)],
        'Wednesday': [(9*60+30, 10*60), (10*60+30, 11*60+30), (12*60+30, 14*60), (16*60, 16*60+30)],
        'Thursday': [(13*60+30, 14*60+30), (15*60, 15*60+30)]
    }
    
    daniel_busy = {
        'Monday': [(10*60, 11*60+30), (12*60+30, 15*60)],
        'Tuesday': [(9*60, 10*60), (10*60+30, 17*60)],
        'Wednesday': [(9*60, 10*60), (10*60+30, 11*60+30), (12*60, 17*60)],
        'Thursday': [(9*60, 12*60), (12*60+30, 14*60+30), (15*60, 15*60+30), (16*60, 17*60)]
    }
    
    for day in days:
        free_m = get_free_slots(megan_busy[day], work_start, work_end)
        free_d = get_free_slots(daniel_busy[day], work_start, work_end)
        
        for slot_m in free_m:
            for slot_d in free_d:
                start_overlap = max(slot_m[0], slot_d[0])
                end_overlap = min(slot_m[1], slot_d[1])
                if end_overlap - start_overlap >= 60:
                    meeting_start = start_overlap
                    meeting_end = meeting_start + 60
                    start_h = meeting_start // 60
                    start_m = meeting_start % 60
                    end_h = meeting_end // 60
                    end_m = meeting_end % 60
                    time_str = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
                    print(day)
                    print(time_str)
                    return

if __name__ == "__main__":
    main()