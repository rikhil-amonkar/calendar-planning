def find_meeting_time():
    days = ["Monday", "Tuesday", "Wednesday"]
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    duration = 60        # 1 hour in minutes

    # Blocks in minutes since midnight
    blocks = {
        "Judith": {
            "Monday": [(12 * 60, 12 * 60 + 30)],
            "Wednesday": [(11 * 60 + 30, 12 * 60)],
        },
        "Timothy": {
            "Monday": [
                (9 * 60 + 30, 10 * 60),
                (10 * 60 + 30, 11 * 60 + 30),
                (12 * 60 + 30, 14 * 60),
                (15 * 60 + 30, 17 * 60)
            ],
            "Tuesday": [
                (9 * 60 + 30, 13 * 60),
                (13 * 60 + 30, 14 * 60),
                (14 * 60 + 30, 17 * 60)
            ],
            "Wednesday": [
                (9 * 60, 9 * 60 + 30),
                (10 * 60 + 30, 11 * 60),
                (13 * 60 + 30, 14 * 60 + 30),
                (15 * 60, 15 * 60 + 30),
                (16 * 60, 16 * 60 + 30)
            ]
        }
    }

    # Preferences: Judith wants to avoid Monday and Wednesday before 12:00
    preferred_days = ["Tuesday", "Wednesday"]
    avoid_wed_before_12 = True

    for day in preferred_days:
        # Skip Monday due to preference
        if day == "Monday":
            continue

        # Generate all possible start times in work hours
        for start in range(work_start, work_end - duration + 1, 15):  # check every 15 minutes
            end = start + duration

            # Check Judith's preference for Wednesday before 12:00
            if day == "Wednesday" and avoid_wed_before_12 and end <= 12 * 60:
                continue

            # Check if slot is free for both
            conflict = False
            for person in ["Judith", "Timothy"]:
                person_blocks = blocks[person].get(day, [])
                for block_start, block_end in person_blocks:
                    if not (end <= block_start or start >= block_end):
                        conflict = True
                        break
                if conflict:
                    break

            if not conflict:
                # Found a slot
                start_str = f"{start // 60:02d}:{start % 60:02d}"
                end_str = f"{end // 60:02d}:{end % 60:02d}"
                return day, start_str, end_str

    # Fallback to Monday if no other day works (though not preferred)
    for start in range(work_start, work_end - duration + 1, 15):
        end = start + duration
        conflict = False
        for person in ["Judith", "Timothy"]:
            person_blocks = blocks[person].get("Monday", [])
            for block_start, block_end in person_blocks:
                if not (end <= block_start or start >= block_end):
                    conflict = True
                    break
            if conflict:
                break
        if not conflict:
            start_str = f"{start // 60:02d}:{start % 60:02d}"
            end_str = f"{end // 60:02d}:{end % 60:02d}"
            return "Monday", start_str, end_str

    return None, None, None

def main():
    day, start_str, end_str = find_meeting_time()
    if day and start_str and end_str:
        print(f"{day}:{start_str}:{end_str}")
    else:
        print("No suitable time found.")

if __name__ == "__main__":
    main()