def minutes_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def intersect_intervals(intervals1, intervals2):
    intersection = []
    for start1, end1 in intervals1:
        for start2, end2 in intervals2:
            start = max(start1, start2)
            end = min(end1, end2)
            if start < end:
                intersection.append((start, end))
    return intersection

def main():
    meeting_duration = 30  # duration in minutes

    # Working hours: 09:00 to 17:00 -> minutes 540 to 1020.
    # Wayne is free the entire day but prefers no meetings before 14:00 (840 minutes).
    wayne_free = [(840, 1020)]
    
    # Melissa is busy during 10:00-11:00, 12:30-14:00, 15:00-15:30.
    # Her free intervals within working hours: 
    # 09:00-10:00  -> (540,600), 11:00-12:30 -> (660,750), 14:00-15:00 -> (840,900), 15:30-17:00 -> (930,1020)
    # After Wayne's constraint (>=14:00), only these count.
    melissa_free = [(840, 900), (930, 1020)]
    
    # Catherine is free all day.
    catherine_free = [(840, 1020)]
    
    # Gregory is busy during 12:30-13:00 and 15:30-16:00.
    # Free intervals: 09:00-12:30 -> (540,750), 13:00-15:30 -> (780,930), 16:00-17:00 -> (960,1020)
    # After applying meeting constraints (>=14:00) we get:
    gregory_free = [(840, 930), (960, 1020)]
    
    # Victoria is busy during 9:00-9:30, 10:30-11:30, 13:00-14:00, 14:30-15:00, 15:30-16:30.
    # Free intervals: 9:30-10:30 -> (570,630), 11:30-13:00 -> (690,780),
    # 14:00-14:30 -> (840,870), 15:00-15:30 -> (900,930), 16:30-17:00 -> (990,1020)
    # After Wayne's constraint:
    victoria_free = [(840, 870), (900, 930), (990, 1020)]
    
    # Thomas is busy during 10:00-12:00, 12:30-13:00, 14:30-16:00.
    # Free intervals: 09:00-10:00 -> (540,600), 12:00-12:30 -> (720,750),
    # 13:00-14:30 -> (780,870), 16:00-17:00 -> (960,1020)
    # With Wayne's constraint:
    thomas_free = [(840, 870), (960, 1020)]
    
    # Jennifer is busy during 9:00-9:30, 10:00-10:30, 11:00-13:00, 13:30-14:30, 15:00-15:30, 16:00-16:30.
    # Free intervals: 9:30-10:00 -> (570,600), 10:30-11:00 -> (630,660),
    # 13:00-13:30 -> (780,810), 14:30-15:00 -> (870,900), 15:30-16:00 -> (930,960), 16:30-17:00 -> (990,1020)
    # After Wayne's constraint, we consider:
    jennifer_free = [(870,900), (930,960), (990,1020)]
    
    # List of all free intervals for each participant after applying constraints.
    free_intervals = [
        wayne_free,
        melissa_free,
        catherine_free,
        gregory_free,
        victoria_free,
        thomas_free,
        jennifer_free
    ]
    
    # Compute the common free intervals by intersecting all participants' free times.
    common = free_intervals[0]
    for intervals in free_intervals[1:]:
        common = intersect_intervals(common, intervals)
    
    # Find the first interval which can accommodate the meeting duration.
    proposed_start, proposed_end = None, None
    for start, end in common:
        if end - start >= meeting_duration:
            proposed_start = start
            proposed_end = start + meeting_duration
            break

    if proposed_start is not None:
        start_str = minutes_to_str(proposed_start)
        end_str = minutes_to_str(proposed_end)
        day = "Monday"
        # Output format: HH:MM:HH:MM and the day of the week
        print(f"{start_str}:{end_str}")
        print(day)
    else:
        print("No available time slot found.")

if __name__ == "__main__":
    main()