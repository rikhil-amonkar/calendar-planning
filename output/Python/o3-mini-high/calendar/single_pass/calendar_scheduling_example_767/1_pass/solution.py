def time_to_minutes(t_str):
    """Convert time string 'HH:MM' to minutes since 00:00."""
    hours, minutes = map(int, t_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes since 00:00 back to time string 'HH:MM'."""
    return f"{m // 60:02d}:{m % 60:02d}"

def subtract_busy(working_start, working_end, busy_intervals):
    """
    Given a working interval [working_start, working_end] and a list of busy intervals,
    return a list of free intervals as (start, end) in minutes.
    """
    free_intervals = []
    current_start = working_start
    for b_start, b_end in sorted(busy_intervals):
        if current_start < b_start:
            free_intervals.append((current_start, b_start))
        # Ensure we skip the busy block
        current_start = max(current_start, b_end)
    if current_start < working_end:
        free_intervals.append((current_start, working_end))
    return free_intervals

def intersect_intervals(list1, list2):
    """Given two lists of intervals, find their intersections."""
    intersections = []
    for start1, end1 in list1:
        for start2, end2 in list2:
            start_int = max(start1, start2)
            end_int = min(end1, end2)
            if start_int < end_int:
                intersections.append((start_int, end_int))
    return intersections

def find_meeting_slot(meeting_duration, working_start, working_end, busy_schedule1, busy_schedule2):
    free1 = subtract_busy(working_start, working_end, busy_schedule1)
    free2 = subtract_busy(working_start, working_end, busy_schedule2)
    possible = intersect_intervals(free1, free2)
    
    # Look for an interval of at least meeting_duration minutes.
    for start, end in sorted(possible):
        if end - start >= meeting_duration:
            return start, start + meeting_duration
    return None, None

def main():
    # Define working hours in minutes (9:00 to 17:00)
    working_start = time_to_minutes("09:00")
    working_end = time_to_minutes("17:00")
    meeting_duration = 60  # minutes
    
    # Define days of interest
    days = ["Monday", "Tuesday", "Wednesday"]
    
    # Calendar busy blocks for each participant per day (as list of tuples (start, end) in minutes)
    martha_schedule = {
        "Monday": [(time_to_minutes("16:00"), time_to_minutes("17:00"))],
        "Tuesday": [(time_to_minutes("15:00"), time_to_minutes("15:30"))],
        "Wednesday": [
            (time_to_minutes("10:00"), time_to_minutes("11:00")),
            (time_to_minutes("14:00"), time_to_minutes("14:30"))
        ]
    }
    
    beverly_schedule = {
        "Monday": [
            (time_to_minutes("09:00"), time_to_minutes("13:30")),
            (time_to_minutes("14:00"), time_to_minutes("17:00"))
        ],
        "Tuesday": [
            (time_to_minutes("09:00"), time_to_minutes("17:00"))
        ],
        "Wednesday": [
            (time_to_minutes("09:30"), time_to_minutes("15:30")),
            (time_to_minutes("16:30"), time_to_minutes("17:00"))
        ]
    }
    
    meeting_day = None
    meeting_start = None
    meeting_end = None
    
    # Loop through the possible days and find the first day with a valid slot.
    for day in days:
        busy_martha = martha_schedule.get(day, [])
        busy_beverly = beverly_schedule.get(day, [])
        start, end = find_meeting_slot(meeting_duration, working_start, working_end, busy_martha, busy_beverly)
        if start is not None:
            meeting_day = day
            meeting_start = start
            meeting_end = end
            break
    
    if meeting_day:
        # Format output as HH:MM:HH:MM along with the day of the week.
        meeting_time_str = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
        print(f"{meeting_day} {meeting_time_str}")
    else:
        print("No available meeting slot found.")

if __name__ == "__main__":
    main()