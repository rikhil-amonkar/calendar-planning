def main():
    work_start = 9 * 60  # 540 minutes (9:00)
    work_end = 17 * 60   # 1020 minutes (17:00)
    days_order = ['Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Monday']

    # Define busy intervals in minutes since midnight
    brian_busy = {
        'Monday': [
            (9*60+30, 10*60),
            (12*60+30, 14*60+30),
            (15*60+30, 16*60),
            (16*60+30, 17*60)
        ],
        'Tuesday': [
            (9*60, 9*60+30)
        ],
        'Wednesday': [
            (12*60+30, 14*60),
            (16*60+30, 17*60)
        ],
        'Thursday': [
            (11*60, 11*60+30),
            (13*60, 13*60+30),
            (16*60+30, 17*60)
        ],
        'Friday': [
            (9*60+30, 10*60),
            (10*60+30, 11*60),
            (13*60, 13*60+30),
            (15*60, 16*60),
            (16*60+30, 17*60)
        ]
    }

    julia_busy = {
        'Monday': [
            (9*60, 10*60),
            (11*60, 11*60+30),
            (12*60+30, 13*60),
            (15*60+30, 16*60)
        ],
        'Tuesday': [
            (13*60, 14*60),
            (16*60, 16*60+30)
        ],
        'Wednesday': [
            (9*60, 11*60+30),
            (12*60, 12*60+30),
            (13*60, 17*60)
        ],
        'Thursday': [
            (9*60, 10*60+30),
            (11*60, 17*60)
        ],
        'Friday': [
            (9*60, 10*60),
            (10*60+30, 11*60+30),
            (12*60+30, 14*60),
            (14*60+30, 15*60),
            (15*60+30, 16*60)
        ]
    }

    def merge_intervals(intervals):
        if not intervals:
            return []
        sorted_intervals = sorted(intervals, key=lambda x: x[0])
        merged = [list(sorted_intervals[0])]
        for current in sorted_intervals[1:]:
            last = merged[-1]
            if current[0] <= last[1]:
                if current[1] > last[1]:
                    merged[-1][1] = current[1]
            else:
                merged.append(list(current))
        return merged

    def get_free_intervals(busy_intervals, work_start, work_end):
        merged = merge_intervals(busy_intervals)
        free = []
        current_start = work_start
        for start, end in merged:
            if start > current_start:
                free.append((current_start, start))
            current_start = max(current_start, end)
        if current_start < work_end:
            free.append((current_start, work_end))
        return free

    def find_overlap(a_start, a_end, b_start, b_end):
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            return (start, end)
        return None

    for day in days_order:
        brian_busy_day = brian_busy.get(day, [])
        julia_busy_day = julia_busy.get(day, [])

        brian_free = get_free_intervals(brian_busy_day, work_start, work_end)
        julia_free = get_free_intervals(julia_busy_day, work_start, work_end)

        overlapping = []
        i = j = 0
        while i < len(brian_free) and j < len(julia_free):
            a_start, a_end = brian_free[i]
            b_start, b_end = julia_free[j]

            overlap = find_overlap(a_start, a_end, b_start, b_end)
            if overlap:
                overlapping.append(overlap)
                if a_end < b_end:
                    i += 1
                else:
                    j += 1
            else:
                if a_start < b_start:
                    i += 1
                else:
                    j += 1

        for start, end in overlapping:
            if end - start >= 60:
                def format_time(minutes):
                    hours = minutes // 60
                    mins = minutes % 60
                    return f"{hours:02d}:{mins:02d}"
                start_str = format_time(start)
                end_str = format_time(start + 60)
                print(f"{day}:{start_str}:{end_str}")
                return

if __name__ == "__main__":
    main()