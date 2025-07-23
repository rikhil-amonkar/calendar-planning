def subtract_busy_intervals(free_intervals, busy_interval):
    b_s, b_e = busy_interval
    new_free = []
    for interval in free_intervals:
        s, e = interval
        if e <= b_s or s >= b_e:
            new_free.append(interval)
        else:
            if s < b_s:
                new_free.append((s, b_s))
            if e > b_e:
                new_free.append((b_e, e))
    return new_free

def main():
    work_start = 540  # 9:00 in minutes
    work_end = 1020    # 17:00 in minutes
    days = ["Monday", "Tuesday"]
    shirley_busy = {
        "Monday": [(630, 660), (720, 750), (960, 990)],
        "Tuesday": [(570, 600)]
    }
    albert_busy = {
        "Monday": [(540, 1020)],
        "Tuesday": [(570, 660), (690, 750), (780, 960), (990, 1020)]
    }
    duration = 30
    preference_threshold = 630  # 10:30 in minutes for Tuesday

    chosen_day = None
    chosen_slot = None

    for day in days:
        free_shirley = [(work_start, work_end)]
        if day in shirley_busy:
            for busy in shirley_busy[day]:
                free_shirley = subtract_busy_intervals(free_shirley, busy)
        
        free_albert = [(work_start, work_end)]
        if day in albert_busy:
            for busy in albert_busy[day]:
                free_albert = subtract_busy_intervals(free_albert, busy)
        
        common_free = []
        for s_int in free_shirley:
            for a_int in free_albert:
                start_overlap = max(s_int[0], a_int[0])
                end_overlap = min(s_int[1], a_int[1])
                if start_overlap < end_overlap and end_overlap - start_overlap >= duration:
                    common_free.append((start_overlap, end_overlap))
        
        if not common_free:
            continue
            
        common_free.sort(key=lambda x: x[0])
        
        if day == "Tuesday":
            preferred = [slot for slot in common_free if slot[1] <= preference_threshold]
            if preferred:
                chosen_slot = preferred[0]
                chosen_day = day
                break
            else:
                chosen_slot = common_free[0]
                chosen_day = day
                break
        else:
            chosen_slot = common_free[0]
            chosen_day = day
            break
    
    s_min, e_min = chosen_slot
    s_hour = s_min // 60
    s_minute = s_min % 60
    e_hour = e_min // 60
    e_minute = e_min % 60
    
    time_str = f"{s_hour:02d}:{s_minute:02d}:{e_hour:02d}:{e_minute:02d}"
    
    print(chosen_day)
    print(time_str)

if __name__ == "__main__":
    main()