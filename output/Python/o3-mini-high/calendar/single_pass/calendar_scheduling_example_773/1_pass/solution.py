def time_to_minutes(t):
    """Converts time string 'HH:MM' to minutes since midnight."""
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Converts minutes since midnight to time string 'HH:MM'."""
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def find_free_slot(busy_intervals, work_start, work_end, duration):
    """
    Given a list of busy intervals (as tuples with minutes), finds the earliest free slot 
    within working hours [work_start, work_end] that is at least 'duration' minutes long.
    Returns a tuple (start, end) in minutes if found, otherwise None.
    """
    # sort the busy intervals by their start times
    busy_intervals.sort()
    free_start = work_start

    for busy_start_time, busy_end_time in busy_intervals:
        # If there is enough free time before the next busy interval,
        # then return the free slot starting at free_start.
        if busy_start_time - free_start >= duration:
            return free_start, free_start + duration
        # Otherwise, update the free_start to the end of this busy interval if it's later.
        free_start = max(free_start, busy_end_time)
    
    # Check if there is free time after the last busy interval.
    if work_end - free_start >= duration:
        return free_start, free_start + duration
    
    return None

def main():
    work_start_str = "09:00"
    work_end_str = "17:00"
    meeting_duration = 60  # Meeting duration in minutes

    work_start = time_to_minutes(work_start_str)
    work_end = time_to_minutes(work_end_str)

    # Roy's busy schedules; Patrick is completely free.
    schedules = {
        "Monday": [("10:00", "11:30"), ("12:00", "13:00"), ("14:00", "14:30"), ("15:00", "17:00")],
        "Tuesday": [("10:30", "11:30"), ("12:00", "14:30"), ("15:00", "15:30"), ("16:00", "17:00")],
        "Wednesday": [("09:30", "11:30"), ("12:30", "14:00"), ("14:30", "15:30"), ("16:30", "17:00")],
    }

    meeting_day = None
    meeting_slot = None

    # Check the days in the requested order: Monday, then Tuesday, then Wednesday.
    for day in ["Monday", "Tuesday", "Wednesday"]:
        busy_intervals = []
        for start_str, end_str in schedules.get(day, []):
            busy_intervals.append((time_to_minutes(start_str), time_to_minutes(end_str)))
        
        slot = find_free_slot(busy_intervals, work_start, work_end, meeting_duration)
        if slot:
            meeting_day = day
            meeting_slot = slot
            break

    if meeting_day and meeting_slot:
        start_time_str = minutes_to_time(meeting_slot[0])
        end_time_str = minutes_to_time(meeting_slot[1])
        # Output format: Day with a time range in the format HH:MM:HH:MM
        print(f"{meeting_day} {start_time_str}:{end_time_str}")
    else:
        print("No available slot found.")

if __name__ == "__main__":
    main()