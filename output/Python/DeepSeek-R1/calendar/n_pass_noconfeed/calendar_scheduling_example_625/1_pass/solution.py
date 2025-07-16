def main():
    # Define work hours: 9:00 to 17:00 (480 minutes from 9:00)
    work_start = 0
    work_end = 480
    
    # Harold's busy intervals in minutes from 9:00
    monday_busy = [[0, 60], [90, 480]]    # 9:00-10:00, 10:30-17:00
    tuesday_busy = [[0, 30], [90, 150], [210, 270], [330, 390], [420, 480]]  # 9:00-9:30, 10:30-11:30, etc.
    
    # Function to compute free intervals
    def compute_free_intervals(busy_intervals, start, end):
        if not busy_intervals:
            return [[start, end]]
        sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
        free = []
        current = start
        for interval in sorted_busy:
            if current < interval[0]:
                free.append([current, interval[0]])
            current = max(current, interval[1])
        if current < end:
            free.append([current, end])
        return free

    monday_free = compute_free_intervals(monday_busy, work_start, work_end)
    tuesday_free = compute_free_intervals(tuesday_busy, work_start, work_end)
    
    # Preference: avoid Monday, and Tuesday before 14:30 (330 minutes from 9:00)
    meeting_start = None
    meeting_end = None
    day = None
    
    # Check Tuesday first (preferred day and time)
    for interval in tuesday_free:
        start, end = interval
        duration = end - start
        # Only consider intervals starting at or after 14:30 (330 minutes)
        if start >= 330 and duration >= 30:
            meeting_start = start
            meeting_end = start + 30  # Take first 30 minutes of the interval
            day = "Tuesday"
            break
    
    # If no suitable Tuesday slot, check Monday
    if day is None:
        for interval in monday_free:
            start, end = interval
            duration = end - start
            if duration >= 30:
                meeting_start = start
                meeting_end = start + 30
                day = "Monday"
                break
    
    # Convert meeting time to string representation
    def min_to_time(minutes):
        total_hours = minutes // 60
        total_minutes = minutes % 60
        hours = 9 + total_hours
        return f"{hours}:{total_minutes:02d}"
    
    start_str = min_to_time(meeting_start)
    end_str = min_to_time(meeting_end)
    time_range = f"{start_str}:{end_str}"
    
    # Output results
    print(day)
    print(time_range)

if __name__ == "__main__":
    main()