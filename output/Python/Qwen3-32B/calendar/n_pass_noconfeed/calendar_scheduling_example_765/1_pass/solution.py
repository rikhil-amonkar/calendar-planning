def time_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy_intervals, work_start=540, work_end=1020):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    merged = []
    for interval in sorted_busy:
        if not merged:
            merged.append(interval)
        else:
            last = merged[-1]
            if interval[0] <= last[1]:
                merged[-1] = (last[0], max(last[1], interval[1]))
            else:
                merged.append(interval)
    free_intervals = []
    prev_end = work_start
    for start, end in merged:
        if prev_end < start:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free_intervals.append((prev_end, work_end))
    return free_intervals

def find_overlaps(intervals1, intervals2):
    i = 0
    j = 0
    overlaps = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        overlap_start = max(start1, start2)
        overlap_end = min(end1, end2)
        if overlap_start < overlap_end:
            overlaps.append((overlap_start, overlap_end))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return overlaps

def main():
    joshua_busy = {
        'Monday': [(15*60, 15*60 + 30)],
        'Tuesday': [(11*60 + 30, 12*60), (13*60, 13*60 + 30), (14*60 + 30, 15*60)],
        'Wednesday': []
    }
    joyce_busy = {
        'Monday': [(9*60, 9*60 + 30), (10*60, 11*60), (11*60 + 30, 12*60 + 30), (13*60, 15*60), (15*60 + 30, 17*60)],
        'Tuesday': [(9*60, 17*60)],
        'Wednesday': [(9*60, 9*60 + 30), (10*60, 11*60), (12*60 + 30, 15*60 + 30), (16*60, 16*60 + 30)]
    }

    days = ['Monday', 'Tuesday', 'Wednesday']
    for day in days:
        joshua_intervals = joshua_busy[day]
        joyce_intervals = joyce_busy[day]

        joshua_free = get_free_intervals(joshua_intervals)
        joyce_free = get_free_intervals(joyce_intervals)

        if day == 'Monday':
            filtered_joyce_free = []
            for start, end in joyce_free:
                if start >= 720:
                    filtered_joyce_free.append((start, end))
            joyce_free = filtered_joyce_free

        overlaps = find_overlaps(joshua_free, joyce_free)
        for start, end in overlaps:
            if end - start >= 30:
                start_time = time_to_str(start)
                end_time = time_to_str(start + 30)
                print(f"{start_time}:{end_time} {day}")
                return

if __name__ == "__main__":
    main()