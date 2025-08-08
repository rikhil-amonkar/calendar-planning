def time_to_minutes(time_str):
    # Converts "HH:MM" to total minutes from midnight.
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    # Converts total minutes from midnight to "HH:MM" format.
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

def get_free_intervals(busy, work_start, work_end):
    """
    Given a list of busy intervals (each a tuple of (start, end) in minutes)
    and the overall work day [work_start, work_end],
    return a list of free intervals.
    """
    free = []
    current = work_start
    for interval in sorted(busy):
        b_start, b_end = interval
        if b_start > current:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(list1, list2):
    """
    Intersect two lists of intervals.
    Each list contains pairs (start, end) in minutes.
    Returns a new list of intervals that are the intersection.
    """
    i, j = 0, 0
    intersections = []
    while i < len(list1) and j < len(list2):
        start1, end1 = list1[i]
        start2, end2 = list2[j]
        # Find overlap between the two intervals.
        start = max(start1, start2)
        end = min(end1, end2)
        if start < end:
            intersections.append((start, end))
        # Move to the next interval in the list that ends earlier.
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersections

def main():
    # Define working hours and meeting duration in minutes.
    work_start = time_to_minutes("09:00")  # 540
    work_end = time_to_minutes("17:00")    # 1020
    meeting_duration = 30  # in minutes

    # Wayne prefers not to have meetings before 14:00.
    wayne_pref_start = time_to_minutes("14:00")  # 840

    # Define busy intervals for each participant in minutes.
    # Each busy interval is represented as a tuple (start, end).
    participants_busy = {
        "Wayne": [  # Free all day.
        ],
        "Melissa": [
            (time_to_minutes("10:00"), time_to_minutes("11:00")),
            (time_to_minutes("12:30"), time_to_minutes("14:00")),
            (time_to_minutes("15:00"), time_to_minutes("15:30")),
        ],
        "Catherine": [
            # No meetings.
        ],
        "Gregory": [
            (time_to_minutes("12:30"), time_to_minutes("13:00")),
            (time_to_minutes("15:30"), time_to_minutes("16:00")),
        ],
        "Victoria": [
            (time_to_minutes("09:00"), time_to_minutes("09:30")),
            (time_to_minutes("10:30"), time_to_minutes("11:30")),
            (time_to_minutes("13:00"), time_to_minutes("14:00")),
            (time_to_minutes("14:30"), time_to_minutes("15:00")),
            (time_to_minutes("15:30"), time_to_minutes("16:30")),
        ],
        "Thomas": [
            (time_to_minutes("10:00"), time_to_minutes("12:00")),
            (time_to_minutes("12:30"), time_to_minutes("13:00")),
            (time_to_minutes("14:30"), time_to_minutes("16:00")),
        ],
        "Jennifer": [
            (time_to_minutes("09:00"), time_to_minutes("09:30")),
            (time_to_minutes("10:00"), time_to_minutes("10:30")),
            (time_to_minutes("11:00"), time_to_minutes("13:00")),
            (time_to_minutes("13:30"), time_to_minutes("14:30")),
            (time_to_minutes("15:00"), time_to_minutes("15:30")),
            (time_to_minutes("16:00"), time_to_minutes("16:30")),
        ]
    }

    # Calculate free intervals for each participant within working hours.
    participants_free = {}
    for person, busy in participants_busy.items():
        participants_free[person] = get_free_intervals(busy, work_start, work_end)

    # Start with the free intervals of the first participant.
    # The order does not matter since we need intersection across everyone.
    common_free = list(participants_free["Wayne"]) if participants_free.get("Wayne") else [(work_start, work_end)]
    for person in participants_free:
        if person == "Wayne":
            continue
        common_free = intersect_intervals(common_free, participants_free[person])

    # Apply Wayne's preference: meeting should not be scheduled before 14:00.
    adjusted_free = []
    for interval in common_free:
        start, end = interval
        new_start = max(start, wayne_pref_start)
        if new_start < end:
            adjusted_free.append((new_start, end))

    # Find the first available slot that can accommodate the meeting.
    meeting_slot = None
    for start, end in adjusted_free:
        if end - start >= meeting_duration:
            meeting_slot = (start, start + meeting_duration)
            break

    # Since a solution is guaranteed, we expect meeting_slot to be found.
    if meeting_slot:
        meeting_start, meeting_end = meeting_slot
        time_range = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
        # Meeting is on Monday.
        print("Monday", time_range)
    else:
        print("No common available time slot found.")

if __name__ == "__main__":
    main()