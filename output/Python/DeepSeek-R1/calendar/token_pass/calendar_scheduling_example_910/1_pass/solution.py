def main():
    work_start = 0  # 9:00 in minutes from 9:00
    work_end = 480   # 17:00 in minutes from 9:00

    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    
    bryan_busy = {
        "Monday": [],
        "Tuesday": [],
        "Wednesday": [],
        "Thursday": [(30, 60), (210, 240)],
        "Friday": [(90, 120), (300, 330)]
    }
    
    nicholas_busy = {
        "Monday": [(150, 180), (240, 390)],
        "Tuesday": [(0, 30), (120, 270), (300, 450)],
        "Wednesday": [(0, 30), (60, 120), (150, 270), (300, 330), (360, 450)],
        "Thursday": [(90, 150), (180, 210), (360, 390), (450, 480)],
        "Friday": [(0, 90), (120, 180), (210, 330), (390, 420), (450, 480)]
    }
    
    avoided_days_bryan = ["Tuesday"]
    avoided_days_nicholas = ["Monday", "Thursday"]
    preferred_days = [day for day in days if day not in avoided_days_bryan and day not in avoided_days_nicholas]
    other_days = [day for day in days if day not in preferred_days]
    
    def get_free_intervals(busy_list, start, end):
        if not busy_list:
            return [(start, end)]
        sorted_busy = sorted(busy_list, key=lambda x: x[0])
        free_intervals = []
        current = start
        for busy in sorted_busy:
            if current < busy[0]:
                free_intervals.append((current, busy[0]))
            current = max(current, busy[1])
        if current < end:
            free_intervals.append((current, end))
        return free_intervals

    def find_overlapping_intervals(intervals1, intervals2):
        overlaps = []
        i, j = 0, 0
        n1, n2 = len(intervals1), len(intervals2)
        while i < n1 and j < n2:
            s1, e1 = intervals1[i]
            s2, e2 = intervals2[j]
            start_max = max(s1, s2)
            end_min = min(e1, e2)
            if start_max < end_min:
                overlaps.append((start_max, end_min))
            if e1 < e2:
                i += 1
            else:
                j += 1
        return overlaps

    def min_to_time(minutes):
        hours = 9 + minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    # Check preferred days first
    for day in preferred_days:
        free_bryan = get_free_intervals(bryan_busy[day], work_start, work_end)
        free_nicholas = get_free_intervals(nicholas_busy[day], work_start, work_end)
        overlaps = find_overlapping_intervals(free_bryan, free_nicholas)
        for start, end in overlaps:
            if end - start >= 60:
                start_time = min_to_time(start)
                end_time = min_to_time(end)
                print(day)
                print(f"{start_time}:{end_time}")
                return

    # If no preferred day, check other days
    for day in other_days:
        free_bryan = get_free_intervals(bryan_busy[day], work_start, work_end)
        free_nicholas = get_free_intervals(nicholas_busy[day], work_start, work_end)
        overlaps = find_overlapping_intervals(free_bryan, free_nicholas)
        for start, end in overlaps:
            if end - start >= 60:
                start_time = min_to_time(start)
                end_time = min_to_time(end)
                print(day)
                print(f"{start_time}:{end_time}")
                return

if __name__ == "__main__":
    main()