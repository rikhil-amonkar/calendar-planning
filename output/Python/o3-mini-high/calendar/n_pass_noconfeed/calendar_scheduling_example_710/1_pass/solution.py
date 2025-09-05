from datetime import datetime

def time_to_minutes(t):
    """Converts time string 'HH:MM' to minutes since midnight."""
    dt = datetime.strptime(t, "%H:%M")
    return dt.hour * 60 + dt.minute

def minutes_to_time(m):
    """Converts minutes since midnight to time string 'HH:MM'."""
    hour = m // 60
    minute = m % 60
    return f"{hour:02d}:{minute:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    """
    Given a list of busy intervals (each a tuple of start and end in minutes)
    and work hours boundaries, returns a list of free intervals within work hours.
    """
    free_intervals = []
    current = work_start
    # Sort busy intervals by their start time.
    busy_intervals = sorted(busy_intervals, key=lambda x: x[0])
    for b_start, b_end in busy_intervals:
        if b_start > current:
            free_intervals.append((current, b_start))
        current = max(current, b_end)
    if current < work_end:
        free_intervals.append((current, work_end))
    return free_intervals

def intersect_intervals(list1, list2):
    """
    Finds the intersection between two lists of intervals.
    Each interval is a tuple (start, end). Returns a list of intersecting intervals.
    """
    i, j = 0, 0
    result = []
    while i < len(list1) and j < len(list2):
        start1, end1 = list1[i]
        start2, end2 = list2[j]
        # Find the overlap between the two intervals.
        start_max = max(start1, start2)
        end_min = min(end1, end2)
        if start_max < end_min:
            result.append((start_max, end_min))
        # Move to the next interval in the list whose end time is earlier.
        if end1 < end2:
            i += 1
        else:
            j += 1
    return result

def find_common_free_interval(free_intervals_list, meeting_duration):
    """
    Given a list of free intervals (list of lists of intervals for each participant),
    find the earliest interval that can accommodate the meeting duration.
    """
    if not free_intervals_list:
        return None
    # Start with the free intervals of the first participant.
    common = free_intervals_list[0]
    # Intersect with the free intervals of each subsequent participant.
    for intervals in free_intervals_list[1:]:
        common = intersect_intervals(common, intervals)
        if not common:
            return None
    # Look for an interval with enough duration.
    for start, end in common:
        if end - start >= meeting_duration:
            return (start, start + meeting_duration)
    return None

def main():
    # Define work hours (in minutes)
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    meeting_duration = 30  # in minutes

    # Busy schedules for each participant
    # Times are in "HH:MM" format.
    schedules = {
        "Cheryl": {
            "Monday": [("09:00", "09:30"), ("11:30", "13:00"), ("15:30", "16:00")],
            "Tuesday": [("15:00", "15:30")]
            # Cheryl cannot meet on Wednesday.
        },
        "Kyle": {
            "Monday": [("09:00", "17:00")],
            "Tuesday": [("09:30", "17:00")],
            "Wednesday": [("09:00", "09:30"), ("10:00", "13:00"), ("13:30", "14:00"), ("14:30", "17:00")]
        }
    }
    
    # Days of week to consider (order matters).
    days = ["Monday", "Tuesday", "Wednesday"]
    
    # Cheryl's constraint: she cannot meet on Wednesday.
    for day in days:
        if day == "Wednesday":
            continue  # Skip Wednesday for Cheryl
        
        free_intervals_list = []
        for person in schedules:
            # If the person has no entry for the day, they are free the whole work day.
            busy_times = schedules[person].get(day, [])
            # Convert busy intervals to minutes.
            busy_minutes = [(time_to_minutes(start), time_to_minutes(end)) for start, end in busy_times]
            free_intervals = get_free_intervals(busy_minutes, work_start, work_end)
            free_intervals_list.append(free_intervals)
        
        # Find a common free interval that can accommodate the meeting.
        meeting_slot = find_common_free_interval(free_intervals_list, meeting_duration)
        if meeting_slot:
            start_time, end_time = meeting_slot
            formatted_start = minutes_to_time(start_time)
            formatted_end = minutes_to_time(end_time)
            print(f"{day} {formatted_start}:{formatted_end}")
            return

if __name__ == "__main__":
    main()