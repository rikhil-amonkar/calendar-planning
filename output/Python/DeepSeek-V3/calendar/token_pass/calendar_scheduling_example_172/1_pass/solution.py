def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    duration = 30        # minutes

    # Busy times in minutes since midnight
    # Each tuple is (start_minute, end_minute)
    patrick_busy = [
        (9*60, 9*60+30),
        (10*60, 10*60+30),
        (13*60+30, 14*60),
        (16*60, 16*60+30)
    ]
    kayla_busy = [
        (12*60+30, 13*60+30),
        (15*60, 15*60+30),
        (16*60, 16*60+30)
    ]
    carl_busy = [
        (10*60+30, 11*60),
        (12*60, 12*60+30),
        (13*60, 13*60+30),
        (14*60+30, 17*60)
    ]
    christian_busy = [
        (9*60, 12*60+30),
        (13*60, 14*60),
        (14*60+30, 17*60)
    ]

    # Combine all busy times per person
    schedules = [patrick_busy, kayla_busy, carl_busy, christian_busy]

    # Check every possible start time from work_start to work_end - duration, in 1-minute increments
    for start in range(work_start, work_end - duration + 1):
        end = start + duration
        conflict = False
        # Check each person's schedule
        for person_busy in schedules:
            person_free = True
            for busy_start, busy_end in person_busy:
                # Check if meeting slot overlaps with busy slot
                if not (end <= busy_start or start >= busy_end):
                    person_free = False
                    break
            if not person_free:
                conflict = True
                break
        if not conflict:
            # Convert start and end to HH:MM format
            start_h = start // 60
            start_m = start % 60
            end_h = end // 60
            end_m = end % 60
            return "Monday", f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
    return None, None

def main():
    day, time_range = find_meeting_time()
    if day and time_range:
        print(f"{day} {time_range}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()