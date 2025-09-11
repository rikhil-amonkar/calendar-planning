def get_available_intervals(work_start, work_end, blocked_intervals):
    available = [(work_start, work_end)]
    blocked_intervals = sorted(blocked_intervals, key=lambda x: x[0])
    for b_start, b_end in blocked_intervals:
        new_available = []
        for a_start, a_end in available:
            if b_end <= a_start:
                new_available.append((a_start, a_end))
            elif b_start >= a_end:
                new_available.append((a_start, a_end))
            else:
                if a_start < b_start:
                    new_available.append((a_start, b_start))
                if a_end > b_end:
                    new_available.append((b_end, a_end))
        available = new_available
    return available

def main():
    work_start = 9 * 60  # 540
    work_end = 17 * 60   # 1020

    # Blocked intervals for each participant
    blocked_bradley = [(570, 600), (750, 780), (810, 840), (930, 960)]
    blocked_teresa = [(630, 660), (720, 750), (780, 810), (870, 900)]
    blocked_elizabeth = [(540, 570), (630, 690), (780, 810), (870, 900), (930, 1020)]
    blocked_christian = [(540, 570), (630, 1020)]

    # Compute available intervals
    available_bradley = get_available_intervals(work_start, work_end, blocked_bradley)
    available_teresa = get_available_intervals(work_start, work_end, blocked_teresa)
    available_elizabeth = get_available_intervals(work_start, work_end, blocked_elizabeth)
    available_christian = get_available_intervals(work_start, work_end, blocked_christian)

    # Find common intervals
    common_intervals = available_bradley
    for available in [available_teresa, available_elizabeth, available_christian]:
        new_common = []
        for interval1 in common_intervals:
            for interval2 in available:
                start = max(interval1[0], interval2[0])
                end = min(interval1[1], interval2[1])
                if start < end:
                    new_common.append((start, end))
        common_intervals = new_common

    # Find the first interval that can fit the 30-minute meeting
    for start, end in common_intervals:
        if end - start >= 30:
            start_h = start // 60
            start_m = start % 60
            end_h = start_h
            end_m = start_m + 30
            if end_m == 60:
                end_m = 0
                end_h += 1
            print(f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d} Monday")
            return

if __name__ == "__main__":
    main()