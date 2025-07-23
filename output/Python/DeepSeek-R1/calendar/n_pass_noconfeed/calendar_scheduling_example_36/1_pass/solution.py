def main():
    # Define work hours: 9:00 to 17:00, but constrained by Denise's preference to end by 12:30
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 12 * 60 + 30  # 12:30 in minutes (meeting must end by this time)
    duration = 60  # meeting duration in minutes

    # Busy intervals in minutes (start inclusive, end exclusive)
    ryan_busy = [(9*60, 9*60+30), (12*60+30, 13*60)]
    ruth_busy = []  # No meetings
    denise_busy = [(9*60+30, 10*60+30), (12*60, 13*60), (14*60+30, 16*60+30)]
    
    # Combine all busy intervals
    all_busy = ryan_busy + ruth_busy + denise_busy
    
    # Clip intervals to the working window [work_start, work_end] and remove empties
    clipped_busy = []
    for start, end in all_busy:
        new_start = max(start, work_start)
        new_end = min(end, work_end)
        if new_start < new_end:
            clipped_busy.append((new_start, new_end))
    
    # Merge overlapping or adjacent intervals
    if not clipped_busy:
        merged_busy = []
    else:
        clipped_busy.sort()
        merged_busy = []
        current_start, current_end = clipped_busy[0]
        for s, e in clipped_busy[1:]:
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged_busy.append((current_start, current_end))
                current_start, current_end = s, e
        merged_busy.append((current_start, current_end))
    
    # Find free intervals within [work_start, work_end]
    free_intervals = []
    prev_end = work_start
    for s, e in merged_busy:
        if s > prev_end:
            free_intervals.append((prev_end, s))
        prev_end = e
    if prev_end < work_end:
        free_intervals.append((prev_end, work_end))
    
    # Find the first free interval that can fit the meeting
    meeting_start = None
    for start, end in free_intervals:
        if end - start >= duration:
            meeting_start = start
            break
    
    if meeting_start is None:
        print("No solution found")
    else:
        meeting_end = meeting_start + duration
        # Convert minutes to HH:MM format
        def format_time(mins):
            h, m = divmod(mins, 60)
            return f"{h:02d}:{m:02d}"
        
        start_str = format_time(meeting_start)
        end_str = format_time(meeting_end)
        print("Monday")
        print(f"{start_str}:{end_str}")

if __name__ == "__main__":
    main()