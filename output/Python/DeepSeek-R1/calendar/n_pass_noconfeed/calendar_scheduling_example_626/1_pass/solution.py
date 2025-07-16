def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    duration = 60

    patricia_tuesday_busy = [
        ("10:00", "10:30"),
        ("11:00", "12:00"),
        ("14:00", "16:00"),
        ("16:30", "17:00")
    ]
    jesse_tuesday_busy = [
        ("11:00", "11:30"),
        ("12:00", "12:30"),
        ("13:00", "14:00"),
        ("14:30", "15:00"),
        ("15:30", "17:00")
    ]

    def compute_free_intervals(busy_intervals, work_start, work_end):
        intervals_in_min = []
        for start_str, end_str in busy_intervals:
            start_min = time_to_minutes(start_str)
            end_min = time_to_minutes(end_str)
            intervals_in_min.append((start_min, end_min))
        intervals_in_min.sort(key=lambda x: x[0])
        
        free_intervals = []
        current_start = work_start
        for start_busy, end_busy in intervals_in_min:
            if current_start < start_busy:
                free_intervals.append((current_start, start_busy))
            current_start = max(current_start, end_busy)
        if current_start < work_end:
            free_intervals.append((current_start, work_end))
        return free_intervals

    patricia_free = compute_free_intervals(patricia_tuesday_busy, work_start, work_end)
    jesse_free = compute_free_intervals(jesse_tuesday_busy, work_start, work_end)

    found_slot = None
    for p_start, p_end in patricia_free:
        for j_start, j_end in jesse_free:
            low = max(p_start, j_start)
            high = min(p_end, j_end)
            if low < high and high - low >= duration:
                found_slot = (low, high)
                break
        if found_slot:
            break

    if found_slot:
        start_time = minutes_to_time(found_slot[0])
        end_time = minutes_to_time(found_slot[0] + duration)
        time_str = f"{start_time}:{end_time}"
        print("Tuesday")
        print(time_str)

if __name__ == '__main__':
    main()