def main():
    # Define work day (Monday) from 9:00 (540 minutes) to 17:00 (1020 minutes)
    work_day_start = 9 * 60  # 540 minutes
    work_day_end = 17 * 60   # 1020 minutes
    work_day = (work_day_start, work_day_end)
    
    # Busy intervals for each participant in minutes (start, end)
    # Each interval is [start, end), meaning busy from start inclusive to end exclusive.
    gregory_busy = [(540, 600), (630, 690), (750, 780), (810, 840)]
    natalie_busy = []  # No busy intervals
    christine_busy = [(540, 690), (810, 1020)]
    vincent_busy = [(540, 570), (630, 720), (750, 840), (870, 1020)]
    
    # List of free intervals for each participant
    participants_busy = [gregory_busy, natalie_busy, christine_busy, vincent_busy]
    free_intervals = []
    
    # Compute free intervals for each participant
    for busy in participants_busy:
        free = []
        current = work_day_start
        # Sort busy intervals by start time
        sorted_busy = sorted(busy, key=lambda x: x[0])
        for interval in sorted_busy:
            start_busy, end_busy = interval
            # If there's a gap between current time and the next busy start
            if current < start_busy:
                free.append((current, start_busy))
            current = max(current, end_busy)
        # After last busy interval, check until work_day_end
        if current < work_day_end:
            free.append((current, work_day_end))
        free_intervals.append(free)
    
    # Function to intersect two sets of intervals
    def intersect_intervals(intervals1, intervals2):
        if not intervals1 or not intervals2:
            return []
        result = []
        i, j = 0, 0
        while i < len(intervals1) and j < len(intervals2):
            a_start, a_end = intervals1[i]
            b_start, b_end = intervals2[j]
            # Calculate overlap
            start_overlap = max(a_start, b_start)
            end_overlap = min(a_end, b_end)
            if start_overlap < end_overlap:
                result.append((start_overlap, end_overlap))
            # Move the pointer for the interval that ends first
            if a_end < b_end:
                i += 1
            else:
                j += 1
        return result
    
    # Compute common free intervals for all participants
    common_free = free_intervals[0]
    for i in range(1, len(free_intervals)):
        common_free = intersect_intervals(common_free, free_intervals[i])
    
    # Find the first common free interval that can fit a 30-minute meeting
    meeting_start = None
    meeting_end = None
    for interval in common_free:
        start, end = interval
        duration = end - start
        if duration >= 30:
            meeting_start = start
            meeting_end = start + 30  # Schedule meeting at the beginning of the interval
            break
    
    # Convert meeting times back to HH:MM format
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    start_time_str = minutes_to_time(meeting_start)
    end_time_str = minutes_to_time(meeting_end)
    
    # Output the time range in the specified format and the day
    time_range_str = f"{start_time_str}:{end_time_str}"
    print("{" + time_range_str + "}")
    print("Monday")

if __name__ == "__main__":
    main()