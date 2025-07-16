from typing import List, Dict, Tuple

def parse_time(time_str: str) -> int:
    """Convert time string in format HH:MM to minutes since 9:00."""
    hh, mm = map(int, time_str.split(':'))
    return (hh - 9) * 60 + mm

def format_time(minutes: int) -> str:
    """Convert minutes since 9:00 back to HH:MM format."""
    hh = 9 + minutes // 60
    mm = minutes % 60
    return f"{hh:02d}:{mm:02d}"

def get_busy_intervals(schedule: Dict[str, List[Tuple[str, str]]], day: str) -> List[Tuple[int, int]]:
    """Get busy intervals for a given day in minutes since 9:00."""
    intervals = []
    for busy_day, busy_times in schedule.items():
        if busy_day == day:
            for start, end in busy_times:
                start_min = parse_time(start)
                end_min = parse_time(end)
                intervals.append((start_min, end_min))
    return intervals

def find_available_slot(busy_intervals: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    """Find an available slot of given duration in minutes."""
    busy_intervals.sort()
    prev_end = 0
    for start, end in busy_intervals:
        if start - prev_end >= duration:
            return (prev_end, prev_end + duration)
        prev_end = max(prev_end, end)
    # Check after last busy interval
    if (17 * 60 - 9 * 60) - prev_end >= duration:
        return (prev_end, prev_end + duration)
    return None

def main():
    # Define work hours (9:00 to 17:00)
    work_start = parse_time("09:00")
    work_end = parse_time("17:00")
    meeting_duration = 60  # minutes

    # Define schedules
    betty_schedule = {
        "Monday": [("10:00", "10:30"), ("11:30", "12:30"), ("16:00", "16:30")],
        "Tuesday": [("9:30", "10:00"), ("10:30", "11:00"), ("12:00", "12:30"), ("13:30", "15:00"), ("16:30", "17:00")],
        "Wednesday": [("13:30", "14:00"), ("14:30", "15:00")],
        "Friday": [("9:00", "10:00"), ("11:30", "12:00"), ("12:30", "13:00"), ("14:30", "15:00")]
    }

    megan_schedule = {
        "Monday": [("9:00", "17:00")],
        "Tuesday": [("9:00", "9:30"), ("10:00", "10:30"), ("12:00", "14:00"), ("15:00", "15:30"), ("16:00", "16:30")],
        "Wednesday": [("9:30", "10:30"), ("11:00", "11:30"), ("12:30", "13:00"), ("13:30", "14:30"), ("15:30", "17:00")],
        "Thursday": [("9:00", "10:30"), ("11:30", "14:00"), ("14:30", "15:00"), ("15:30", "16:30")],
        "Friday": [("9:00", "17:00")]
    }

    # Betty cannot meet on Wednesday or Thursday
    days_to_check = ["Monday", "Tuesday", "Friday"]

    for day in days_to_check:
        # Get busy intervals for both participants
        betty_busy = get_busy_intervals(betty_schedule, day)
        megan_busy = get_busy_intervals(megan_schedule, day)

        # Combine and merge busy intervals
        all_busy = betty_busy + megan_busy
        all_busy.sort()

        # Find available slot
        slot = find_available_slot(all_busy, meeting_duration)
        if slot:
            start, end = slot
            start_time = format_time(start)
            end_time = format_time(end)
            print(f"{day}: {start_time}:{end_time}")
            return

    print("No available slot found.")

if __name__ == "__main__":
    main()