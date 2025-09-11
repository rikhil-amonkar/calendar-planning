def main():
    duration = 60
    work_start = 0
    work_end = 480

    kayla_blocks = [(60, 90), (330, 420)]
    rebecca_blocks = [(0, 240), (270, 360), (390, 420)]

    kayla_free = find_free_intervals(work_start, work_end, kayla_blocks)
    rebecca_free = find_free_intervals(work_start, work_end, rebecca_blocks)

    common_free = find_common_intervals(kayla_free, rebecca_free)

    for start, end in common_free:
        if end - start >= duration:
            meeting_start = start
            meeting_end = meeting_start + duration
            start_hour = 9 + meeting_start // 60
            start_minute = meeting_start % 60
            end_hour = 9 + meeting_end // 60
            end_minute = meeting_end % 60
            time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
            print(f"Monday {time_str}")
            return

    print("No suitable time found.")

def find_free_intervals(work_start, work_end, blocks):
    sorted_blocks = sorted(blocks, key=lambda x: x[0])
    free_intervals = []
    current = work_start
    for block_start, block_end in sorted_blocks:
        if current < block_start:
            free_intervals.append((current, block_start))
        current = max(current, block_end)
    if current < work_end:
        free_intervals.append((current, work_end))
    return free_intervals

def find_common_intervals(intervals1, intervals2):
    common = []
    i = j = 0
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        start_max = max(start1, start2)
        end_min = min(end1, end2)
        if start_max < end_min:
            common.append((start_max, end_min))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return common

if __name__ == "__main__":
    main()