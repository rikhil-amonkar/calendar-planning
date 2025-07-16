def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return (hours - 9) * 60 + minutes

def minutes_to_time(mins):
    total_minutes = mins
    hours = 9 + total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(busy_intervals, work_start=0, work_end=480):
    if not busy_intervals:
        return [(work_start, work_end)]
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    if sorted_busy[0][0] > work_start:
        free.append((work_start, sorted_busy[0][0]))
    for i in range(len(sorted_busy) - 1):
        if sorted_busy[i][1] < sorted_busy[i+1][0]:
            free.append((sorted_busy[i][1], sorted_busy[i+1][0]))
    if sorted_busy[-1][1] < work_end:
        free.append((sorted_busy[-1][1], work_end))
    return free

def intersect_two_intervals(intervals_a, intervals_b):
    i, j = 0, 0
    result = []
    while i < len(intervals_a) and j < len(intervals_b):
        a_start, a_end = intervals_a[i]
        b_start, b_end = intervals_b[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            result.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return result

def intersect_multiple_intervals(intervals_list):
    if not intervals_list:
        return []
    current = intervals_list[0]
    for i in range(1, len(intervals_list)):
        current = intersect_two_intervals(current, intervals_list[i])
    return current

def main():
    work_start = 0
    work_end = 480
    constraint_start = 300  # 14:00

    persons_busy_minutes = {
        "Natalie": [],
        "David": [
            (time_to_minutes("11:30"), time_to_minutes("12:00")),
            (time_to_minutes("14:30"), time_to_minutes("15:00"))
        ],
        "Douglas": [
            (time_to_minutes("9:30"), time_to_minutes("10:00")),
            (time_to_minutes("11:30"), time_to_minutes("12:00")),
            (time_to_minutes("13:00"), time_to_minutes("13:30")),
            (time_to_minutes("14:30"), time_to_minutes("15:00"))
        ],
        "Ralph": [
            (time_to_minutes("9:00"), time_to_minutes("9:30")),
            (time_to_minutes("10:00"), time_to_minutes("11:00")),
            (time_to_minutes("11:30"), time_to_minutes("12:30")),
            (time_to_minutes("13:30"), time_to_minutes("15:00")),
            (time_to_minutes("15:30"), time_to_minutes("16:00")),
            (time_to_minutes("16:30"), time_to_minutes("17:00"))
        ],
        "Jordan": [
            (time_to_minutes("9:00"), time_to_minutes("10:00")),
            (time_to_minutes("12:00"), time_to_minutes("12:30")),
            (time_to_minutes("13:00"), time_to_minutes("13:30")),
            (time_to_minutes("14:30"), time_to_minutes("15:00")),
            (time_to_minutes("15:30"), time_to_minutes("17:00"))
        ]
    }

    free_intervals_per_person = []
    for person, busy_list in persons_busy_minutes.items():
        free_intervals = get_free_intervals(busy_list, work_start, work_end)
        free_intervals_per_person.append(free_intervals)

    common_free = intersect_multiple_intervals(free_intervals_per_person)
    
    common_after_constraint = []
    for s, e in common_free:
        low = max(s, constraint_start)
        high = min(e, work_end)
        if low < high:
            common_after_constraint.append((low, high))
    
    meeting_start = None
    for s, e in common_after_constraint:
        if e - s >= 30:
            meeting_start = s
            break
    
    if meeting_start is None:
        # According to the problem, there is a solution, so this should not happen.
        meeting_start = constraint_start
    
    start_time_str = minutes_to_time(meeting_start)
    end_time_str = minutes_to_time(meeting_start + 30)
    time_range_str = f"{start_time_str}:{end_time_str}"
    
    print("Monday")
    print(time_range_str)

if __name__ == "__main__":
    main()