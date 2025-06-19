def convert_to_minutes(time_str):
    """Convert 'HH:MM' string to minutes since midnight."""
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def convert_to_time(minutes):
    """Convert minutes since midnight to 'HH:MM' format with two-digit hour."""
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

def merge_intervals(intervals):
    """Merge overlapping intervals."""
    if not intervals:
        return []
    
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = []
    current_start, current_end = sorted_intervals[0]
    
    for s, e in sorted_intervals[1:]:
        if s <= current_end:
            current_end = max(current_end, e)
        else:
            merged.append((current_start, current_end))
            current_start, current_end = s, e
    merged.append((current_start, current_end))
    
    return merged

def find_free_intervals(busy_intervals, work_start, work_end):
    """Find free time intervals within work hours."""
    if not busy_intervals:
        return [(work_start, work_end)] if work_start < work_end else []
    
    merged_busy = merge_intervals(busy_intervals)
    free = []
    current = work_start
    
    for s, e in merged_busy:
        if current < s:
            free.append((current, s))
        current = e
    
    if current < work_end:
        free.append((current, work_end))
    
    return free

def main():
    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60
    work_end = 17 * 60

    # Define busy times in minutes since midnight
    jean_busy = {
        'Monday': [],
        'Tuesday': [
            (convert_to_minutes("11:30"), convert_to_minutes("12:00")),
            (convert_to_minutes("16:00"), convert_to_minutes("16:30"))
        ]
    }
    doris_busy = {
        'Monday': [
            (convert_to_minutes("9:00"), convert_to_minutes("11:30")),
            (convert_to_minutes("12:00"), convert_to_minutes("12:30")),
            (convert_to_minutes("13:30"), convert_to_minutes("16:00")),
            (convert_to_minutes("16:30"), convert_to_minutes("17:00"))
        ],
        'Tuesday': [
            (convert_to_minutes("9:00"), convert_to_minutes("17:00"))
        ]
    }

    candidate_day = None
    candidate_time = None

    # Check days in order: Monday first, then Tuesday
    for day in ['Monday', 'Tuesday']:
        # Combine busy intervals from both participants
        combined_busy = jean_busy[day] + doris_busy[day]
        
        # Calculate free intervals for this day
        free_intervals = find_free_intervals(combined_busy, work_start, work_end)
        
        # Check each free interval for valid meeting times
        for start, end in free_intervals:
            duration = end - start
            if duration < 30:  # Skip intervals shorter than meeting duration
                continue
                
            # On Monday, meeting must end by 14:00 (840 minutes)
            meeting_end = start + 30
            if day == 'Monday':
                if meeting_end > 14 * 60:
                    continue  # Doesn't satisfy Monday constraint
            
            # Found valid candidate - earliest possible on this day
            candidate_day = day
            candidate_time = (start, meeting_end)
            break
        
        if candidate_day:
            break  # Found earliest valid day/time
    
    # Output results
    if candidate_day:
        start_time = convert_to_time(candidate_time[0])
        end_time = convert_to_time(candidate_time[1])
        print(candidate_day)
        print(f"{start_time}:{end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()