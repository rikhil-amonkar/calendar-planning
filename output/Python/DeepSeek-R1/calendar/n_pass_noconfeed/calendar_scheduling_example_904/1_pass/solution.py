def compute_free_intervals(busy_intervals, work_start, work_end):
    if not busy_intervals:
        return [(work_start, work_end)]
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current = work_start
    for s, e in sorted_busy:
        if s > current:
            free.append((current, s))
        current = max(current, e)
    if current < work_end:
        free.append((current, work_end))
    return free

def main():
    # Day is forced to be Tuesday due to constraints
    day = "Tuesday"
    # Work hours: 9:00 to 17:00, but only consider from 12:00 onwards
    work_start = 12 * 60  # 12:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes

    # Daniel's busy intervals on Tuesday (converted to half-open [start, end))
    daniel_busy = [
        (13*60, 13*60 + 30),   # 13:00-13:30 -> [780, 810)
        (15*60 + 30, 16*60),    # 15:30-16:00 -> [930, 960)
        (16*60 + 30, 17*60)     # 16:30-17:00 -> [990, 1020)
    ]

    # Bradley's busy intervals on Tuesday (converted to half-open [start, end))
    bradley_busy = [
        (12*60, 13*60),         # 12:00-13:00 -> [720, 780)
        (13*60 + 30, 14*60),    # 13:30-14:00 -> [810, 840)
        (15*60 + 30, 16*60 + 30) # 15:30-16:30 -> [930, 990)
    ]

    # Compute free intervals within [work_start, work_end)
    free_daniel = compute_free_intervals(daniel_busy, work_start, work_end)
    free_bradley = compute_free_intervals(bradley_busy, work_start, work_end)

    # Find the first overlapping free interval of at least 30 minutes
    meeting_start = None
    for d_int in free_daniel:
        for b_int in free_bradley:
            start_overlap = max(d_int[0], b_int[0])
            end_overlap = min(d_int[1], b_int[1])
            if end_overlap - start_overlap >= 30:
                meeting_start = start_overlap
                break
        if meeting_start is not None:
            break

    # Format the meeting time
    if meeting_start is None:
        # According to the problem, a solution exists, so this should not happen
        print("No solution found")
    else:
        meeting_end = meeting_start + 30
        # Convert minutes to HH:MM format
        def format_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"
        
        start_str = format_time(meeting_start)
        end_str = format_time(meeting_end)
        time_range_str = f"{start_str}:{end_str}"
        print(day)
        print(time_range_str)

if __name__ == "__main__":
    main()