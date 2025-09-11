def main():
    work_start = 0  # 9:00
    work_end = 480  # 17:00

    laura_busy_monday = [(90, 120), (210, 240), (330, 390), (420, 480)]
    philip_busy_monday = [(0, 480)]

    laura_busy_tuesday = [(30, 60), (120, 150), (240, 270), (330, 360), (420, 480)]
    philip_busy_tuesday = [(0, 120), (150, 180), (240, 270), (300, 330), (360, 450)]

    laura_busy_thursday = [(90, 120), (180, 270), (360, 390), (420, 450)]
    philip_busy_thursday = [(0, 90), (120, 210), (240, 480)]

    days = {
        "Monday": (laura_busy_monday, philip_busy_monday),
        "Tuesday": (laura_busy_tuesday, philip_busy_tuesday),
        "Thursday": (laura_busy_thursday, philip_busy_thursday)
    }

    for day, (laura_busy, philip_busy) in days.items():
        laura_free = find_free_intervals(laura_busy, work_start, work_end)
        philip_free = find_free_intervals(philip_busy, work_start, work_end)
        common_free = find_overlapping_intervals(laura_free, philip_free)
        for start, end in common_free:
            if end - start >= 60:
                start_str = min_to_time(start)
                end_str = min_to_time(end)
                print(f"{day} {start_str}:{end_str}")
                return

    print("No suitable time found.")

def find_free_intervals(busy_intervals, start, end):
    busy_sorted = sorted(busy_intervals, key=lambda x: x[0])
    free_intervals = []
    current = start
    for busy_start, busy_end in busy_sorted:
        if current < busy_start:
            free_intervals.append((current, busy_start))
        current = max(current, busy_end)
    if current < end:
        free_intervals.append((current, end))
    return free_intervals

def find_overlapping_intervals(intervals1, intervals2):
    overlapping = []
    i = j = 0
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        start_overlap = max(start1, start2)
        end_overlap = min(end1, end2)
        if start_overlap < end_overlap:
            overlapping.append((start_overlap, end_overlap))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return overlapping

def min_to_time(minutes):
    hours = 9 + minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

if __name__ == "__main__":
    main()