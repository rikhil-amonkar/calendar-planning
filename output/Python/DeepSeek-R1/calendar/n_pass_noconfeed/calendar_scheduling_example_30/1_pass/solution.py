def main():
    # Convert time string to minutes since midnight
    def time_to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m

    # Convert minutes to time string (HH:MM)
    def minutes_to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"

    # Define work hours and meeting duration
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    meeting_duration = 30
    preference_threshold = time_to_minutes("14:00")  # 14:00 in minutes

    # Define busy intervals for each participant (in minutes since midnight)
    jeffrey_busy = [
        ("9:30", "10:00"),
        ("10:30", "11:00")
    ]
    jeffrey_intervals = [(time_to_minutes(s), time_to_minutes(e)) for s, e in jeffrey_busy]

    virginia_busy = [
        ("9:00", "9:30"),
        ("10:00", "10:30"),
        ("14:30", "15:00"),
        ("16:00", "16:30")
    ]
    virginia_intervals = [(time_to_minutes(s), time_to_minutes(e)) for s, e in virginia_busy]

    melissa_busy = [
        ("9:00", "11:30"),
        ("12:00", "12:30"),
        ("13:00", "15:00"),
        ("16:00", "17:00")
    ]
    melissa_intervals = [(time_to_minutes(s), time_to_minutes(e)) for s, e in melissa_busy]

    # Combine all busy intervals
    all_busy = jeffrey_intervals + virginia_intervals + melissa_intervals
    
    # Sort by start time
    all_busy.sort(key=lambda x: x[0])
    
    # Merge overlapping intervals
    merged = []
    if all_busy:
        current_start, current_end = all_busy[0]
        for start, end in all_busy[1:]:
            if start <= current_end:
                current_end = max(current_end, end)
            else:
                merged.append((current_start, current_end))
                current_start, current_end = start, end
        merged.append((current_start, current_end))
    
    # Find free intervals within work hours
    free_intervals = []
    start = work_start
    for busy_start, busy_end in merged:
        if start < busy_start:
            free_intervals.append((start, busy_start))
        start = busy_end
    if start < work_end:
        free_intervals.append((start, work_end))
    
    # Find the earliest suitable meeting time
    candidate_preferred = None
    candidate_non_preferred = None
    
    for start_free, end_free in free_intervals:
        available_duration = end_free - start_free
        if available_duration >= meeting_duration:
            meeting_start = start_free
            meeting_end = meeting_start + meeting_duration
            # Check if meeting ends before preference threshold (14:00)
            if meeting_end <= preference_threshold:
                candidate_preferred = (meeting_start, meeting_end)
                break
            elif candidate_non_preferred is None:
                candidate_non_preferred = (meeting_start, meeting_end)
    
    # Determine which candidate to use
    if candidate_preferred:
        meeting_start, meeting_end = candidate_preferred
    elif candidate_non_preferred:
        meeting_start, meeting_end = candidate_non_preferred
    else:
        # According to the problem, there is a solution, so this should not happen
        raise Exception("No suitable time found")
    
    # Format the meeting time
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    time_range_str = f"{start_str}:{end_str}"
    
    # Output the day and time range
    print("Monday")
    print(time_range_str)

if __name__ == "__main__":
    main()