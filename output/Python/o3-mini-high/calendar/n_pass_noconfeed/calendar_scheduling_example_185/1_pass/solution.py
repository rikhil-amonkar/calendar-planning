def get_free_intervals(busy_intervals, work_start, work_end):
    """
    Given a sorted list of busy intervals (each as a (start, end) in minutes),
    return a list of free intervals between work_start and work_end.
    """
    free_intervals = []
    current = work_start
    for b_start, b_end in busy_intervals:
        if b_start > current:
            free_intervals.append((current, b_start))
        current = max(current, b_end)
    if current < work_end:
        free_intervals.append((current, work_end))
    return free_intervals

def intersect_intervals(intervals1, intervals2):
    """
    Given two lists of intervals, compute their intersection.
    Each interval is a tuple (start, end) in minutes.
    """
    i, j = 0, 0
    intersections = []
    while i < len(intervals1) and j < len(intervals2):
        start = max(intervals1[i][0], intervals2[j][0])
        end = min(intervals1[i][1], intervals2[j][1])
        if start < end:
            intersections.append((start, end))
        # Move to the next interval in the list with the earliest end time
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return intersections

def minutes_to_str(minutes):
    """Convert a minutes-from-midnight integer into a HH:MM string."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    # Define working hours in minutes (9:00 to 17:00)
    work_start = 9 * 60   # 540
    work_end = 17 * 60    # 1020

    # Meeting duration in minutes (30 minutes)
    meeting_duration = 30

    # Busy schedules (times in minutes from midnight)
    # Kimberly's busy intervals: 10:00-10:30, 11:00-12:00, 16:00-16:30
    kimberly_busy = [(10*60, 10*60+30), (11*60, 12*60), (16*60, 16*60+30)]
    # Megan has no meetings but would like to avoid meetings before 10:00.
    megan_busy = []  # We will adjust her available time below.
    # Marie's busy intervals: 10:00-11:00, 11:30-15:00, 16:00-16:30
    marie_busy = [(10*60, 11*60), (11*60+30, 15*60), (16*60, 16*60+30)]
    # Diana's busy intervals: 9:30-10:00, 10:30-14:30, 15:30-17:00
    diana_busy = [(9*60+30, 10*60), (10*60+30, 14*60+30), (15*60+30, 17*60)]

    # Get free intervals for each participant.
    kimberly_free = get_free_intervals(kimberly_busy, work_start, work_end)
    # For Megan, adjust the work_start to 10:00 to respect her preference.
    megan_free = get_free_intervals(megan_busy, max(work_start, 10*60), work_end)
    marie_free    = get_free_intervals(marie_busy, work_start, work_end)
    diana_free    = get_free_intervals(diana_busy, work_start, work_end)

    # Intersect free intervals for all participants.
    common_free = intersect_intervals(kimberly_free, megan_free)
    common_free = intersect_intervals(common_free, marie_free)
    common_free = intersect_intervals(common_free, diana_free)

    meeting_start = None
    meeting_end = None

    # Look for an interval with sufficient duration.
    for start, end in common_free:
        if (end - start) >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            break

    if meeting_start is not None:
        meeting_time_str = f"{minutes_to_str(meeting_start)}:{minutes_to_str(meeting_end)}"
        day_of_week = "Monday"
        print(day_of_week)
        print(meeting_time_str)
    else:
        print("No available meeting time found.")

if __name__ == "__main__":
    main()