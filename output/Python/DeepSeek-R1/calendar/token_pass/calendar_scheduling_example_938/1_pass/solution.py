def get_free_intervals(busy_list, start_time=0, end_time=480):
    if not busy_list:
        return [(start_time, end_time)]
    sorted_busy = sorted(busy_list, key=lambda x: x[0])
    free_list = []
    current = start_time
    for busy in sorted_busy:
        if current < busy[0]:
            free_list.append((current, busy[0]))
        current = max(current, busy[1])
    if current < end_time:
        free_list.append((current, end_time))
    return free_list

def find_common_free(free1, free2):
    common = []
    i = j = 0
    while i < len(free1) and j < len(free2):
        start1, end1 = free1[i]
        start2, end2 = free2[j]
        start_max = max(start1, start2)
        end_min = min(end1, end2)
        if start_max < end_min:
            common.append((start_max, end_min))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return common

def minutes_to_time(minutes):
    hours = 9 + minutes // 60
    minutes_remain = minutes % 60
    return f"{hours:02d}:{minutes_remain:02d}"

def main():
    eugene_busy = {
        "Monday": [(120, 180), (270, 300), (330, 360), (420, 450)],
        "Tuesday": [],
        "Wednesday": [(0, 30), (120, 150), (180, 210), (270, 360)],
        "Thursday": [(30, 60), (120, 210)],
        "Friday": [(90, 120), (180, 210), (240, 270)]
    }
    
    eric_busy = {
        "Monday": [(0, 480)],
        "Tuesday": [(0, 480)],
        "Wednesday": [(0, 150), (180, 300), (330, 450)],
        "Thursday": [(0, 480)],
        "Friday": [(0, 120), (150, 480)]
    }
    
    days = ["Friday", "Monday", "Tuesday", "Thursday", "Wednesday"]
    
    for day in days:
        eugene_free = get_free_intervals(eugene_busy.get(day, []))
        eric_free = get_free_intervals(eric_busy.get(day, []))
        common_free = find_common_free(eugene_free, eric_free)
        for start, end in common_free:
            if end - start >= 30:
                meeting_start = start
                meeting_end = meeting_start + 30
                start_str = minutes_to_time(meeting_start)
                end_str = minutes_to_time(meeting_end)
                print(f"{day} {start_str}:{end_str}")
                return
                
    print("No suitable time found.")

if __name__ == "__main__":
    main()