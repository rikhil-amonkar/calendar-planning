def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    # Work hours in minutes
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    meeting_duration = 60  # minutes

    # Busy intervals for Gary and David on Monday and Tuesday
    # Each interval is (start_minute, end_minute)
    gary_monday = [
        (time_to_minutes("9:30"), time_to_minutes("10:00")),
        (time_to_minutes("11:00"), time_to_minutes("13:00")),
        (time_to_minutes("14:00"), time_to_minutes("14:30")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
    gary_tuesday = [
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("14:30"), time_to_minutes("16:00"))
    ]
    david_monday = [
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("10:00"), time_to_minutes("13:00")),
        (time_to_minutes("14:30"), time_to_minutes("16:30"))
    ]
    david_tuesday = [
        (time_to_minutes("9:00"), time_to_minutes("9:30")),
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("14:30")),
        (time_to_minutes("15:00"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
    
    days = ["Monday", "Tuesday"]
    all_busy = {
        "Monday": gary_monday + david_monday,
        "Tuesday": gary_tuesday + david_tuesday
    }
    
    # Process each day
    for day in days:
        busy_intervals = all_busy[day]
        # Sort by start time
        busy_intervals.sort(key=lambda x: x[0])
        merged_busy = []
        if busy_intervals:
            current_start, current_end = busy_intervals[0]
            for i in range(1, len(busy_intervals)):
                start, end = busy_intervals[i]
                if start <= current_end:
                    if end > current_end:
                        current_end = end
                else:
                    merged_busy.append((current_start, current_end))
                    current_start, current_end = start, end
            merged_busy.append((current_start, current_end))
        else:
            merged_busy = []
        
        # Free intervals: from work_start to work_end, excluding merged_busy
        free_intervals = []
        current = work_start
        for start, end in merged_busy:
            if current < start:
                free_intervals.append((current, start))
            current = end
        if current < work_end:
            free_intervals.append((current, work_end))
        
        # Check for a free interval that can fit the meeting
        for start, end in free_intervals:
            if end - start >= meeting_duration:
                meeting_start = start
                meeting_end = meeting_start + meeting_duration
                # Format the output as HH:MM:HH:MM and day
                start_str = minutes_to_time(meeting_start)
                end_str = minutes_to_time(meeting_end)
                print(f"{day}:{start_str}:{end_str}")
                return
    
    # If no slot found (though the problem states there is a solution)
    print("No suitable time found")

if __name__ == "__main__":
    main()