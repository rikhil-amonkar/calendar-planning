def minutes_to_time_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def has_conflict(start, duration, busy_intervals):
    end = start + duration
    for b_start, b_end in busy_intervals:
        # Check if the meeting [start, end] overlaps with a busy interval [b_start, b_end]
        if start < b_end and end > b_start:
            return True
    return False

def is_valid_slot(start, duration, all_busy):
    # Returns True if none of the participants have a conflict at [start, start+duration]
    for busy in all_busy:
        if has_conflict(start, duration, busy):
            return False
    return True

def find_meeting_slot():
    meeting_duration = 60  # in minutes

    # Define working hours for Monday (9:00 to 17:00) in minutes (since midnight)
    work_start = 9 * 60      # 540 minutes => 09:00
    work_end = 17 * 60       # 1020 minutes => 17:00

    # Pamela's constraint: Do not meet after 14:30 (i.e., meeting must end by 14:30)
    latest_end_allowed = 14 * 60 + 30  # 14:30 -> 870 minutes
    # Thus, meeting must start no later than:
    latest_possible_start = latest_end_allowed - meeting_duration  # 870 - 60 = 810 (i.e., 13:30)

    # Busy intervals in minutes for each participant on Monday
    anthony_busy = [
        (9 * 60 + 30, 10 * 60),   # 09:30 to 10:00
        (12 * 60, 13 * 60),       # 12:00 to 13:00
        (16 * 60, 16 * 60 + 30)   # 16:00 to 16:30
    ]

    pamela_busy = [
        (9 * 60 + 30, 10 * 60),   # 09:30 to 10:00
        (16 * 60 + 30, 17 * 60)   # 16:30 to 17:00
    ]

    zachary_busy = [
        (9 * 60, 11 * 60 + 30),    # 09:00 to 11:30
        (12 * 60, 12 * 60 + 30),   # 12:00 to 12:30
        (13 * 60, 13 * 60 + 30),   # 13:00 to 13:30
        (14 * 60 + 30, 15 * 60),   # 14:30 to 15:00
        (16 * 60, 17 * 60)         # 16:00 to 17:00
    ]

    # Gather all busy schedules
    all_busy = [anthony_busy, pamela_busy, zachary_busy]

    # Look for a valid start time between work_start and latest_possible_start (inclusive)
    for start in range(work_start, latest_possible_start + 1):
        # Even though work_end is 17:00, Pamela's constraint forces us to have the meeting end by 14:30.
        if start + meeting_duration > latest_end_allowed:
            break
        if is_valid_slot(start, meeting_duration, all_busy):
            return start, start + meeting_duration

    return None, None

def main():
    meeting_start, meeting_end = find_meeting_slot()
    if meeting_start is not None:
        start_str = minutes_to_time_str(meeting_start)
        end_str = minutes_to_time_str(meeting_end)
        # Output in the format HH:MM:HH:MM along with the day of the week "Monday"
        print(f"Monday {start_str}:{end_str}")
    else:
        print("No available meeting slot was found for Monday.")

if __name__ == "__main__":
    main()