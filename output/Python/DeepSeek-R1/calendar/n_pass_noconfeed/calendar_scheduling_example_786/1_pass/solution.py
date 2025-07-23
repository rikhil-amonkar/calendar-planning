def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

def get_free_intervals(work_start, work_end, busy_list):
    if not busy_list:
        return [(work_start, work_end)]
    sorted_busy = sorted(busy_list, key=lambda x: x[0])
    free = []
    current = work_start
    for start, end in sorted_busy:
        if current < start:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(list1, list2):
    if not list1 or not list2:
        return []
    i = j = 0
    intersections = []
    while i < len(list1) and j < len(list2):
        a1, a2 = list1[i]
        b1, b2 = list2[j]
        low = max(a1, b1)
        high = min(a2, b2)
        if low < high:
            intersections.append((low, high))
        if a2 < b2:
            i += 1
        else:
            j += 1
    return intersections

def main():
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    days = ["Monday", "Tuesday", "Wednesday"]
    
    busy_amy = {
        "Monday": [],
        "Tuesday": [],
        "Wednesday": [
            (time_to_minutes("11:00"), time_to_minutes("11:30")),
            (time_to_minutes("13:30"), time_to_minutes("14:00"))
        ]
    }
    
    busy_pamela = {
        "Monday": [
            (time_to_minutes("9:00"), time_to_minutes("10:30")),
            (time_to_minutes("11:00"), time_to_minutes("16:30"))
        ],
        "Tuesday": [
            (time_to_minutes("9:00"), time_to_minutes("9:30")),
            (time_to_minutes("10:00"), time_to_minutes("17:00"))
        ],
        "Wednesday": [
            (time_to_minutes("9:00"), time_to_minutes("9:30")),
            (time_to_minutes("10:00"), time_to_minutes("11:00")),
            (time_to_minutes("11:30"), time_to_minutes("13:30")),
            (time_to_minutes("14:30"), time_to_minutes("15:00")),
            (time_to_minutes("16:00"), time_to_minutes("16:30"))
        ]
    }
    
    candidates = []
    for day in days:
        free_amy = get_free_intervals(work_start, work_end, busy_amy[day])
        free_pamela = get_free_intervals(work_start, work_end, busy_pamela[day])
        free_both = intersect_intervals(free_amy, free_pamela)
        
        for s, e in free_both:
            duration = e - s
            if duration < 30:
                continue
                
            if day in ["Tuesday", "Wednesday"]:
                after_start = max(s, 960)
                if after_start + 30 <= e and after_start + 30 <= work_end:
                    priority = 1 if day == "Wednesday" else 2
                    candidates.append((day, after_start, after_start + 30, priority))
                
                before_end = min(e, 960)
                if before_end - s >= 30:
                    priority = 3 if day == "Wednesday" else 4
                    candidates.append((day, s, s + 30, priority))
            else:
                if s + 30 <= e:
                    candidates.append((day, s, s + 30, 5))
    
    if not candidates:
        print("No solution found")
        return
        
    candidates.sort(key=lambda x: x[3])
    best_candidate = candidates[0]
    day, start_min, end_min, _ = best_candidate
    start_time = minutes_to_time(start_min)
    end_time = minutes_to_time(end_min)
    print(day)
    print(f"{start_time}:{end_time}")

if __name__ == "__main__":
    main()