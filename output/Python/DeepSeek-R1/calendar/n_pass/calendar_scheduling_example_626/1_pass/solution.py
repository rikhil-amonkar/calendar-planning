def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def main():
    work_start = "09:00"
    work_end = "17:00"
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    
    patricia_busy = {
        'Monday': [
            ('10:00', '10:30'),
            ('11:30', '12:00'),
            ('13:00', '13:30'),
            ('14:30', '15:30'),
            ('16:00', '16:30')
        ],
        'Tuesday': [
            ('10:00', '10:30'),
            ('11:00', '12:00'),
            ('14:00', '16:00'),
            ('16:30', '17:00')
        ]
    }
    
    jesse_busy = {
        'Monday': [
            ('9:00', '17:00')
        ],
        'Tuesday': [
            ('11:00', '11:30'),
            ('12:00', '12:30'),
            ('13:00', '14:00'),
            ('14:30', '15:00'),
            ('15:30', '17:00')
        ]
    }
    
    def get_free_intervals(busy_list, work_start_min, work_end_min):
        busy_min = []
        for interval in busy_list:
            s_min = time_to_minutes(interval[0])
            e_min = time_to_minutes(interval[1])
            busy_min.append((s_min, e_min))
        
        free_intervals = [(work_start_min, work_end_min)]
        for (busy_s, busy_e) in busy_min:
            new_free = []
            for (fs, fe) in free_intervals:
                if busy_e <= fs or busy_s >= fe:
                    new_free.append((fs, fe))
                else:
                    if fs < busy_s:
                        new_free.append((fs, busy_s))
                    if busy_e < fe:
                        new_free.append((busy_e, fe))
            free_intervals = new_free
        return free_intervals

    days = ['Monday', 'Tuesday']
    for day in days:
        free_patricia = get_free_intervals(patricia_busy[day], work_start_min, work_end_min)
        free_jesse = get_free_intervals(jesse_busy[day], work_start_min, work_end_min)
        
        common_free = []
        for intv1 in free_patricia:
            for intv2 in free_jesse:
                start = max(intv1[0], intv2[0])
                end = min(intv1[1], intv2[1])
                if start < end:
                    common_free.append((start, end))
        
        common_free.sort(key=lambda x: x[0])
        for (s, e) in common_free:
            if e - s >= 60:
                meeting_start = s
                meeting_end = s + 60
                s_h = meeting_start // 60
                s_m = meeting_start % 60
                e_h = meeting_end // 60
                e_m = meeting_end % 60
                time_str = f"{s_h:02d}:{s_m:02d}:{e_h:02d}:{e_m:02d}"
                print(day)
                print(time_str)
                return

if __name__ == "__main__":
    main()