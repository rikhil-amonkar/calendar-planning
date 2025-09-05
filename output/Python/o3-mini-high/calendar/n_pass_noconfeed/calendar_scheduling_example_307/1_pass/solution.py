def minutes_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def is_slot_free(start, duration, busy_intervals):
    end = start + duration
    for b_start, b_end in busy_intervals:
        # Check if the meeting interval [start, end) overlaps with a busy interval
        if start < b_end and end > b_start:
            return False
    return True

def main():
    meeting_duration = 30  # duration in minutes
    day = "Monday"
    work_start = 9 * 60   # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes

    # Busy intervals for each participant (times in minutes after midnight)
    busy = {
        "Ronald": [],
        "Stephen": [(10 * 60, 10 * 60 + 30), (12 * 60, 12 * 60 + 30)],
        "Brittany": [(11 * 60, 11 * 60 + 30), (13 * 60 + 30, 14 * 60),
                     (15 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)],
        "Dorothy": [(9 * 60, 9 * 60 + 30), (10 * 60, 10 * 60 + 30),
                    (11 * 60, 12 * 60 + 30), (13 * 60, 15 * 60), (15 * 60 + 30, 17 * 60)],
        "Rebecca": [(9 * 60 + 30, 10 * 60 + 30), (11 * 60, 11 * 60 + 30),
                    (12 * 60, 12 * 60 + 30), (13 * 60, 17 * 60)],
        "Jordan": [(9 * 60, 9 * 60 + 30), (10 * 60, 11 * 60),
                   (11 * 60 + 30, 12 * 60), (13 * 60, 15 * 60), (15 * 60 + 30, 16 * 60 + 30)]
    }

    meeting_start = None

    # Loop through each possible start time within work hours.
    # We use minute granularity.
    for t in range(work_start, work_end - meeting_duration + 1):
        slot_free = True
        for person, intervals in busy.items():
            if not is_slot_free(t, meeting_duration, intervals):
                slot_free = False
                break
        if slot_free:
            meeting_start = t
            break

    if meeting_start is not None:
        start_str = minutes_to_str(meeting_start)
        end_str = minutes_to_str(meeting_start + meeting_duration)
        print(f"{day} {start_str}:{end_str}")
    else:
        print("No available meeting time found.")

if __name__ == "__main__":
    main()