def minutes_to_str(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def find_available_slot(busy_intervals, work_start, work_end, duration):
    # Sort the busy intervals by start time
    busy_intervals = sorted(busy_intervals, key=lambda x: x[0])
    current = work_start
    
    # Check gap before the first busy time
    for start_busy, end_busy in busy_intervals:
        if start_busy - current >= duration:
            return current, current + duration
        current = max(current, end_busy)
    
    # Check gap after the last busy interval until work end
    if work_end - current >= duration:
        return current, current + duration
    
    return None  # No available slot found

def main():
    # Define workday start and end in minutes (9:00 to 17:00)
    work_start = 9 * 60     # 9:00 AM => 540 minutes
    work_end = 17 * 60      # 17:00 PM => 1020 minutes
    meeting_duration = 30   # Meeting duration in minutes

    # Define Samuel's busy schedules (in minutes) for Monday, Tuesday, Wednesday.
    # Note: Larry is available all day, but his preference is to avoid Wednesday.
    calendars = {
        "Monday": [
            (10 * 60 + 30, 11 * 60),      # 10:30 - 11:00
            (12 * 60, 12 * 60 + 30),       # 12:00 - 12:30
            (13 * 60, 15 * 60),            # 13:00 - 15:00
            (15 * 60 + 30, 16 * 60 + 30)   # 15:30 - 16:30
        ],
        "Tuesday": [
            (9 * 60, 12 * 60),            # 9:00 - 12:00
            (14 * 60, 15 * 60 + 30),       # 14:00 - 15:30
            (16 * 60 + 30, 17 * 60)        # 16:30 - 17:00
        ],
        "Wednesday": [
            (10 * 60 + 30, 11 * 60),       # 10:30 - 11:00
            (11 * 60 + 30, 12 * 60),       # 11:30 - 12:00
            (12 * 60 + 30, 13 * 60),       # 12:30 - 13:00
            (14 * 60, 14 * 60 + 30),       # 14:00 - 14:30
            (15 * 60, 16 * 60)             # 15:00 - 16:00
        ]
    }

    # Order of preference: Monday (best), then Tuesday, then Wednesday (Larry prefers not Wednesday)
    preferred_days = ["Monday", "Tuesday", "Wednesday"]

    for day in preferred_days:
        busy_slots = calendars[day]
        slot = find_available_slot(busy_slots, work_start, work_end, meeting_duration)
        if slot:
            start, end = slot
            start_str = minutes_to_str(start)
            end_str = minutes_to_str(end)
            print(f"{day} {start_str}:{end_str}")
            return

if __name__ == "__main__":
    main()