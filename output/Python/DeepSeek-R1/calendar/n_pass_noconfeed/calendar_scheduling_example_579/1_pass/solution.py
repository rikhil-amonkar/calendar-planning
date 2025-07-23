def main():
    # Define work hours: 9:00 to 17:00 in minutes (540 to 1020), but due to Helen's constraint, we only consider until 15:00 (900)
    work_start = 540  # 9:00
    work_end = 900    # 15:00

    # Christine's busy intervals within the considered time range [540, 900]
    christine_busy = [
        [660, 690]   # 11:00-11:30
    ]

    # Helen's busy intervals within [540, 900] (adjusted for her "cannot meet after 15:00" constraint)
    helen_busy = [
        [570, 630],  # 9:30-10:30
        [660, 690],  # 11:00-11:30
        [720, 750],  # 12:00-12:30
        [810, 900]   # 13:30-15:00
    ]

    # Compute free intervals for Christine
    free_christine = []
    current = work_start
    for s, e in sorted(christine_busy, key=lambda x: x[0]):
        if current < s:
            free_christine.append([current, s])
        current = max(current, e)
    if current < work_end:
        free_christine.append([current, work_end])

    # Compute free intervals for Helen
    free_helen = []
    current = work_start
    for s, e in sorted(helen_busy, key=lambda x: x[0]):
        if current < s:
            free_helen.append([current, s])
        current = max(current, e)
    if current < work_end:
        free_helen.append([current, work_end])

    # Find the first overlapping free interval of at least 30 minutes
    meeting_start = None
    for c_int in free_christine:
        for h_int in free_helen:
            start_overlap = max(c_int[0], h_int[0])
            end_overlap = min(c_int[1], h_int[1])
            if end_overlap - start_overlap >= 30:  # 30 minutes meeting
                meeting_start = start_overlap
                meeting_end = meeting_start + 30
                break
        if meeting_start is not None:
            break

    # Convert meeting time to HH:MM format
    start_hour = meeting_start // 60
    start_minute = meeting_start % 60
    end_hour = meeting_end // 60
    end_minute = meeting_end % 60

    # Format as HH:MM:HH:MM string
    time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
    print("Monday", time_str)

if __name__ == "__main__":
    main()