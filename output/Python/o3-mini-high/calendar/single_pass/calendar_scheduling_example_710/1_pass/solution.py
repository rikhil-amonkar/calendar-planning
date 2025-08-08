def minutes_to_time(minutes):
    """Convert minutes since midnight to a HH:MM formatted string."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def is_slot_free(candidate_start, candidate_end, busy_intervals):
    """Check if the candidate slot [candidate_start, candidate_end] does not overlap with any busy interval."""
    for busy_start, busy_end in busy_intervals:
        # Overlap if candidate_start < busy_end and candidate_end > busy_start
        if candidate_start < busy_end and candidate_end > busy_start:
            return False
    return True

def main():
    # Meeting parameters
    meeting_duration = 30  # in minutes
    work_start = 9 * 60    # 9:00 in minutes
    work_end = 17 * 60     # 17:00 in minutes

    # Days to consider
    days = ["Monday", "Tuesday", "Wednesday"]

    # Busy schedules for each participant in minutes from midnight.
    schedules = {
        "Cheryl": {
            "Monday": [(9 * 60, 9 * 60 + 30), (11 * 60 + 30, 13 * 60), (15 * 60 + 30, 16 * 60)],
            "Tuesday": [(15 * 60, 15 * 60 + 30)],
            "Wednesday": []  # Cheryl cannot meet on Wednesday.
        },
        "Kyle": {
            "Monday": [(9 * 60, 17 * 60)],
            "Tuesday": [(9 * 60 + 30, 17 * 60)],
            "Wednesday": [(9 * 60, 9 * 60 + 30), (10 * 60, 13 * 60), (13 * 60 + 30, 14 * 60), (14 * 60 + 30, 17 * 60)]
        }
    }

    # Iterate over each day in order.
    for day in days:
        # Cheryl cannot meet on Wednesday.
        if day == "Wednesday":
            continue

        # Try each possible starting minute within work hours.
        for candidate_start in range(work_start, work_end - meeting_duration + 1):
            candidate_end = candidate_start + meeting_duration

            # Check availability for Cheryl and Kyle on the current day.
            if (is_slot_free(candidate_start, candidate_end, schedules["Cheryl"].get(day, [])) and
                is_slot_free(candidate_start, candidate_end, schedules["Kyle"].get(day, []))):
                # Found a valid meeting slot.
                start_str = minutes_to_time(candidate_start)
                end_str = minutes_to_time(candidate_end)
                print(f"{day} {start_str}:{end_str}")
                return

    print("No suitable meeting time found.")

if __name__ == "__main__":
    main()