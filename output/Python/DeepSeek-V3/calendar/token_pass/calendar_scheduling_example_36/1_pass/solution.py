def time_to_minutes(t):
    """Convert HH:MM to minutes since midnight."""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes since midnight to HH:MM."""
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def main():
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    duration = 60  # minutes

    # Busy times in minutes since midnight
    ryan_busy = [(time_to_minutes("9:00"), time_to_minutes("9:30")),
                 (time_to_minutes("12:30"), time_to_minutes("13:00"))]
    denise_busy = [(time_to_minutes("9:30"), time_to_minutes("10:30")),
                   (time_to_minutes("12:00"), time_to_minutes("13:00")),
                   (time_to_minutes("14:30"), time_to_minutes("16:30"))]
    ruth_busy = []  # No meetings

    # Denise's cutoff: not after 12:30
    denise_cutoff = time_to_minutes("12:30")

    # Generate free slots for each person within work hours
    def free_slots(busy_list, work_start, work_end, extra_constraint_end=None):
        busy_sorted = sorted(busy_list, key=lambda x: x[0])
        free = []
        current_start = work_start

        for start_busy, end_busy in busy_sorted:
            if start_busy > current_start:
                free.append((current_start, min(start_busy, extra_constraint_end) if extra_constraint_end else start_busy))
            current_start = max(current_start, end_busy)
        if current_start < (extra_constraint_end if extra_constraint_end else work_end):
            free.append((current_start, extra_constraint_end if extra_constraint_end else work_end))
        # Filter out zero-length slots and adjust for extra_constraint_end
        free = [(s, e) for s, e in free if e > s and s < (extra_constraint_end if extra_constraint_end else work_end)]
        if extra_constraint_end:
            free = [(s, min(e, extra_constraint_end)) for s, e in free]
        return free

    ryan_free = free_slots(ryan_busy, work_start, work_end)
    ruth_free = free_slots(ruth_busy, work_start, work_end)
    denise_free = free_slots(denise_busy, work_start, work_end, denise_cutoff)

    # Intersect free slots
    def intersect_slots(slots1, slots2):
        i, j = 0, 0
        intersections = []
        while i < len(slots1) and j < len(slots2):
            start1, end1 = slots1[i]
            start2, end2 = slots2[j]
            intersect_start = max(start1, start2)
            intersect_end = min(end1, end2)
            if intersect_start < intersect_end:
                intersections.append((intersect_start, intersect_end))
            if end1 < end2:
                i += 1
            else:
                j += 1
        return intersections

    # Intersect all three
    intersect_ry_ruth = intersect_slots(ryan_free, ruth_free)
    intersect_all = intersect_slots(intersect_ry_ruth, denise_free)

    # Find a slot of at least 'duration' minutes
    meeting_slot = None
    for start, end in intersect_all:
        if end - start >= duration:
            meeting_slot = (start, start + duration)
            break

    if meeting_slot:
        start_time, end_time = meeting_slot
        print(f"{minutes_to_time(start_time)}:{minutes_to_time(end_time)}")
        print("Monday")
    else:
        print("No suitable slot found")

if __name__ == "__main__":
    main()