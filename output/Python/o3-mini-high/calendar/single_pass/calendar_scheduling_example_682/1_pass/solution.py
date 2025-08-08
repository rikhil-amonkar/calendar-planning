def minutes_to_str(m):
    """Convert minutes since midnight to HH:MM string."""
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def get_free_intervals(window, busy_list):
    """
    Given a time window (start, end) and a sorted list of busy intervals,
    return the free intervals within the window.
    Times are in minutes from midnight.
    """
    free = []
    start, end = window
    current = start
    for b in busy_list:
        # adjust busy interval to the window boundaries
        b_start = max(start, b[0])
        b_end = min(end, b[1])
        if b_end <= current:
            continue
        if b_start > current:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < end:
        free.append((current, end))
    return free

def intersect_intervals(list1, list2):
    """
    Given two lists of intervals, compute their intersections.
    """
    intersections = []
    for int1 in list1:
        for int2 in list2:
            s = max(int1[0], int2[0])
            e = min(int1[1], int2[1])
            if s < e:
                intersections.append((s, e))
    return intersections

def find_meeting_slot(intersections, duration):
    """
    From a list of intersected intervals, find the first slot that
    can accommodate the meeting of given duration (in minutes).
    Returns the meeting start and end times in minutes.
    """
    for slot in intersections:
        if slot[1] - slot[0] >= duration:
            return slot[0], slot[0] + duration
    return None

def main():
    meeting_duration = 30  # minutes

    # Working hours for a standard day: 9:00 - 17:00 (but may be limited by constraints).
    WORK_START = 9 * 60  # 540
    WORK_END = 17 * 60   # 1020

    # Define participants' busy schedules in minutes.
    # Format: (start_in_minutes, end_in_minutes)
    # Monday schedules (not used because Nathan cannot meet on Monday).
    amanda_busy = {
        "Monday": [(9*60, 10*60+30), (11*60, 11*60+30), (12*60+30, 13*60), (13*60+30, 14*60), (14*60+30, 15*60)],
        "Tuesday": [(9*60, 9*60+30), (10*60, 10*60+30), (11*60+30, 12*60), (13*60+30, 14*60+30), (15*60+30, 16*60), (16*60+30, 17*60)]
    }
    nathan_busy = {
        "Monday": [(10*60, 10*60+30), (11*60, 11*60+30), (13*60+30, 14*60+30), (16*60, 16*60+30)],
        "Tuesday": [(9*60, 10*60+30), (11*60, 13*60), (13*60+30, 14*60), (14*60+30, 15*60+30), (16*60, 16*60+30)]
    }

    # Constraints:
    # - Amanda does not want to meet on Tuesday after 11:00.
    # - Nathan cannot meet on Monday.
    # Therefore we only consider Tuesday.
    day = "Tuesday"
    # For Tuesday, Amanda's constraint forces the meeting to be before 11:00.
    # So restrict the meeting window to 9:00 - 11:00.
    effective_work_end = min(WORK_END, 11 * 60)  # 11:00 is 11*60 = 660
    meeting_window = (WORK_START, effective_work_end)

    # Get busy intervals for Tuesday from each participant.
    amanda_busy_intervals = amanda_busy.get(day, [])
    nathan_busy_intervals = nathan_busy.get(day, [])

    # Compute free intervals within the meeting window for each.
    amanda_free = get_free_intervals(meeting_window, amanda_busy_intervals)
    nathan_free = get_free_intervals(meeting_window, nathan_busy_intervals)

    # Compute overlapping free intervals.
    common_free = intersect_intervals(amanda_free, nathan_free)

    slot = find_meeting_slot(common_free, meeting_duration)
    if slot:
        start_str = minutes_to_str(slot[0])
        end_str = minutes_to_str(slot[1])
        # Output in the format: "HH:MM:HH:MM Day" (e.g., "10:30:11:00 Tuesday")
        print(f"{start_str}:{end_str} {day}")
    else:
        print("No common slot available.")

if __name__ == "__main__":
    main()