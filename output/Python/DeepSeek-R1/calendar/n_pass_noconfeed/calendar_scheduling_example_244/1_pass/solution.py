def main():
    # Define work hours in minutes (9:00 to 17:00)
    work_start = 9 * 60  # 540 minutes
    work_end = 17 * 60   # 1020 minutes
    meeting_duration = 30  # minutes

    # Collect all busy intervals (in minutes) from every participant
    all_busy = []
    # Walter: no meetings
    # Cynthia: 9:00-9:30, 10:00-10:30, 13:30-14:30, 15:00-16:00
    all_busy.extend([[540, 570], [600, 630], [810, 870], [900, 960]])
    # Ann: 10:00-11:00, 13:00-13:30, 14:00-15:00, 16:00-16:30
    all_busy.extend([[600, 660], [780, 810], [840, 900], [960, 990]])
    # Catherine: 9:00-11:30, 12:30-13:30, 14:30-17:00
    all_busy.extend([[540, 690], [750, 810], [870, 1020]])
    # Kyle: 9:00-9:30, 10:00-11:30, 12:00-12:30, 13:00-14:30, 15:00-16:00
    all_busy.extend([[540, 570], [600, 690], [720, 750], [780, 870], [900, 960]])

    # Sort all busy intervals by start time
    all_busy.sort(key=lambda x: x[0])

    # Merge overlapping or adjacent intervals
    merged = []
    current_start, current_end = all_busy[0]
    for i in range(1, len(all_busy)):
        s, e = all_busy[i]
        if s <= current_end:
            current_end = max(current_end, e)
        else:
            merged.append([current_start, current_end])
            current_start, current_end = s, e
    merged.append([current_start, current_end])

    # Calculate free intervals within work hours
    free_intervals = []
    # Check before first busy interval
    if merged[0][0] > work_start:
        free_intervals.append([work_start, merged[0][0]])
    # Check between merged intervals
    for i in range(len(merged) - 1):
        gap_start = merged[i][1]
        gap_end = merged[i+1][0]
        if gap_end > gap_start:  # Valid gap exists
            free_intervals.append([gap_start, gap_end])
    # Check after last busy interval
    if merged[-1][1] < work_end:
        free_intervals.append([merged[-1][1], work_end])

    # Find the first free interval that can fit the meeting
    for interval in free_intervals:
        start_min, end_min = interval
        if end_min - start_min >= meeting_duration:
            meeting_start = start_min
            meeting_end = meeting_start + meeting_duration
            # Convert meeting times to HH:MM format
            start_hour = meeting_start // 60
            start_minute = meeting_start % 60
            end_hour = meeting_end // 60
            end_minute = meeting_end % 60
            start_str = f"{start_hour:02d}:{start_minute:02d}"
            end_str = f"{end_hour:02d}:{end_minute:02d}"
            print("Monday")
            print(f"{start_str}:{end_str}")
            return

    # Fallback in case no slot is found (though problem states a solution exists)
    print("Monday")
    print("No suitable time found")

if __name__ == "__main__":
    main()