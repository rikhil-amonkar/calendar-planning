def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    # Meeting parameters
    day = "Monday"
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    duration_minutes = 30
    
    # Lisa's busy intervals in minutes (start, end) - end exclusive
    lisa_busy = [
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("14:00"), time_to_minutes("16:00"))
    ]
    
    # Anthony's busy intervals
    anthony_busy = [
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:30"), time_to_minutes("13:30")),
        (time_to_minutes("14:00"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
    
    # Function to get free intervals from busy intervals
    def get_free_intervals(busy, start, end):
        busy_sorted = sorted(busy, key=lambda x: x[0])
        free = []
        current = start
        
        for interval in busy_sorted:
            if current < interval[0]:
                free.append((current, interval[0]))
            current = max(current, interval[1])
        if current < end:
            free.append((current, end))
            
        return free
    
    # Get free intervals for Lisa and Anthony
    lisa_free = get_free_intervals(lisa_busy, work_start, work_end)
    anthony_free = get_free_intervals(anthony_busy, work_start, work_end)
    
    # Find overlapping free intervals
    common_free = []
    for l_start, l_end in lisa_free:
        for a_start, a_end in anthony_free:
            start_overlap = max(l_start, a_start)
            end_overlap = min(l_end, a_end)
            if start_overlap < end_overlap and (end_overlap - start_overlap) >= duration_minutes:
                common_free.append((start_overlap, end_overlap))
    
    # Find the earliest available slot
    if common_free:
        # Sort by start time to get earliest
        common_free.sort(key=lambda x: x[0])
        start_meeting, end_meeting = common_free[0]
        # Take the earliest possible meeting slot (first 30 minutes of the common free interval)
        meeting_end = start_meeting + duration_minutes
        # Format the meeting time
        start_str = minutes_to_time(start_meeting)
        end_str = minutes_to_time(meeting_end)
        # Output day and time range in HH:MM:HH:MM format
        print(day)
        print(f"{start_str}:{end_str}")
    else:
        # According to the problem, there is a solution, so this should not happen
        print("No available slot found")

if __name__ == "__main__":
    main()