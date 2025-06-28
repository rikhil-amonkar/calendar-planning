def time_str_to_minutes(time_str):
    h, m = time_str.split(':')
    return int(h) * 60 + int(m)

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def compute_free(work_start, work_end, busy_list):
    if not busy_list:
        return [(work_start, work_end)]
    sorted_busy = sorted(busy_list, key=lambda x: x[0])
    free = []
    current_start = work_start
    for s, e in sorted_busy:
        if s < current_start:
            if e > current_start:
                current_start = e
            continue
        if current_start < s:
            free.append((current_start, s))
        current_start = max(current_start, e)
    if current_start < work_end:
        free.append((current_start, work_end))
    return free

def main():
    days = ['Monday', 'Wednesday', 'Tuesday']
    work_start = 9 * 60  # 9:00
    work_end = 17 * 60   # 17:00

    susan_busy = {
        'Monday': [(12*60+30, 13*60), (13*60+30, 14*60)],
        'Tuesday': [(11*60+30, 12*60)],
        'Wednesday': [(9*60+30, 10*60+30), (14*60, 14*60+30), (15*60+30, 16*60+30)]
    }

    sandra_busy = {
        'Monday': [(9*60, 13*60), (14*60, 15*60)],
        'Tuesday': [(9*60, 9*60+30), (10*60+30, 12*60), (12*60+30, 13*60+30), (14*60, 14*60+30), (16*60, 17*60)],
        'Wednesday': [(9*60, 11*60+30), (12*60, 12*60+30), (13*60, 17*60)]
    }

    for day in days:
        susan_work = (work_start, work_end)
        if day == 'Monday':
            sandra_work = (work_start, 16*60)
        else:
            sandra_work = (work_start, work_end)
            
        susan_free = compute_free(susan_work[0], susan_work[1], susan_busy.get(day, []))
        sandra_free = compute_free(sandra_work[0], sandra_work[1], sandra_busy.get(day, []))
        
        for s1, e1 in susan_free:
            for s2, e2 in sandra_free:
                start_overlap = max(s1, s2)
                end_overlap = min(e1, e2)
                if end_overlap - start_overlap >= 30:
                    start_time = minutes_to_time(start_overlap)
                    end_time = minutes_to_time(start_overlap + 30)
                    time_output = f"{start_time.replace(':', '')}:{end_time.replace(':', '')}"
                    print(day)
                    print(time_output)
                    return
                    
    print("No suitable time found")

if __name__ == "__main__":
    main()