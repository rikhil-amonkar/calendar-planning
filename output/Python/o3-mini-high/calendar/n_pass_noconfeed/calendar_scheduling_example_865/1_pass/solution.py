def minutes_to_str(m):
    """Convert minutes since midnight to HH:MM string."""
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def is_slot_free(busy_intervals, start, end):
    """
    Check if the time slot [start, end) (in minutes) is free given busy intervals.
    The intervals are assumed to be half-open: [busy_start, busy_end).
    """
    for b_start, b_end in busy_intervals:
        # There is an overlap if the meeting starts before a busy interval ends
        # and ends after the busy interval starts.
        if start < b_end and end > b_start:
            return False
    return True

def find_meeting_time(schedules, work_start, work_end, duration, days):
    """
    Find the earliest one-hour time slot across the given days where every participant is free.
    'schedules' is a dictionary keyed by participant name with values being a dictionary
    mapping day names to a list of busy intervals (start, end) in minutes.
    """
    # Iterate through days in the given order.
    for day in days:
        # Try every possible start time in minutes from work_start to latest allowable start.
        for start_time in range(work_start, work_end - duration + 1):
            end_time = start_time + duration
            available = True
            # Check each participant's busy schedule for the day.
            for person in schedules:
                # Get the busy intervals for the day; if none, assume completely free.
                busy_intervals = schedules[person].get(day, [])
                if not is_slot_free(busy_intervals, start_time, end_time):
                    available = False
                    break
            if available:
                return day, start_time, end_time
    return None, None, None

def main():
    # Define workday boundaries and meeting duration (in minutes)
    work_start = 9 * 60   # 9:00 AM -> 540 minutes
    work_end = 17 * 60    # 5:00 PM -> 1020 minutes
    meeting_duration = 60  # one hour meeting

    # Days to consider for the meeting
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

    # Define busy schedules for each participant.
    # Times are represented as minutes since midnight.
    schedules = {
        "Megan": {
            "Monday": [(13 * 60, 13 * 60 + 30), (14 * 60, 15 * 60 + 30)],
            "Tuesday": [(9 * 60, 9 * 60 + 30), (12 * 60, 12 * 60 + 30), (16 * 60, 17 * 60)],
            "Wednesday": [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 11 * 60 + 30), (12 * 60 + 30, 14 * 60), (16 * 60, 16 * 60 + 30)],
            "Thursday": [(13 * 60 + 30, 14 * 60 + 30), (15 * 60, 15 * 60 + 30)]
        },
        "Daniel": {
            "Monday": [(10 * 60, 11 * 60 + 30), (12 * 60 + 30, 15 * 60)],
            "Tuesday": [(9 * 60, 10 * 60), (10 * 60 + 30, 17 * 60)],
            "Wednesday": [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60 + 30), (12 * 60, 17 * 60)],
            "Thursday": [(9 * 60, 12 * 60), (12 * 60 + 30, 14 * 60 + 30), (15 * 60, 15 * 60 + 30), (16 * 60, 17 * 60)]
        }
    }

    # Find the earliest available meeting slot.
    day, start, end = find_meeting_time(schedules, work_start, work_end, meeting_duration, days)
    if day is not None:
        # Format the meeting time as HH:MM:HH:MM
        start_str = minutes_to_str(start)
        end_str = minutes_to_str(end)
        print(f"{day} {{{start_str}:{end_str}}}")
    else:
        print("No common available time slot found.")

if __name__ == "__main__":
    main()