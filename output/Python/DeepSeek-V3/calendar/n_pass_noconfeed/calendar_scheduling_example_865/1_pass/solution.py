from typing import List, Dict, Tuple

def parse_time(time_str: str) -> int:
    """Convert time string in HH:MM format to minutes since 9:00 (start of workday)."""
    hh, mm = map(int, time_str.split(':'))
    return (hh - 9) * 60 + mm

def format_time(minutes: int) -> str:
    """Convert minutes since 9:00 back to HH:MM format."""
    hh = 9 + minutes // 60
    mm = minutes % 60
    return f"{hh:02d}:{mm:02d}"

def find_earliest_meeting_slot(
    participants: List[Dict[str, List[Tuple[int, int]]]],
    days: List[str],
    meeting_duration: int,
    work_start: int = 0,  # 9:00 in minutes since 9:00
    work_end: int = 480   # 17:00 in minutes since 9:00 (8 hours)
) -> Tuple[str, str]:
    """
    Find the earliest available meeting slot for all participants.
    
    Args:
        participants: List of participants' busy slots per day.
        days: List of days to consider.
        meeting_duration: Duration of the meeting in minutes.
        work_start: Start of workday in minutes since 9:00.
        work_end: End of workday in minutes since 9:00.
    
    Returns:
        Tuple of (day, time_range) in format "HH:MM-HH:MM".
    """
    for day_idx, day in enumerate(days):
        # Collect all busy slots for the day across participants
        busy_slots = []
        for participant in participants:
            busy_slots.extend(participant[day])
        
        # Merge overlapping or adjacent busy slots
        if not busy_slots:
            return day, f"{format_time(work_start)}-{format_time(work_start + meeting_duration)}"
        
        busy_slots.sort()
        merged = [busy_slots[0]]
        for start, end in busy_slots[1:]:
            last_start, last_end = merged[-1]
            if start <= last_end:
                merged[-1] = (last_start, max(end, last_end))
            else:
                merged.append((start, end))
        
        # Check the slot before the first busy slot
        first_start, first_end = merged[0]
        if first_start - work_start >= meeting_duration:
            return day, f"{format_time(work_start)}-{format_time(work_start + meeting_duration)}"
        
        # Check slots between busy slots
        for i in range(1, len(merged)):
            prev_end = merged[i-1][1]
            curr_start = merged[i][0]
            if curr_start - prev_end >= meeting_duration:
                return day, f"{format_time(prev_end)}-{format_time(prev_end + meeting_duration)}"
        
        # Check the slot after the last busy slot
        last_start, last_end = merged[-1]
        if work_end - last_end >= meeting_duration:
            return day, f"{format_time(last_end)}-{format_time(last_end + meeting_duration)}"
    
    raise ValueError("No suitable meeting time found.")

def main():
    # Define participants' busy slots (in minutes since 9:00)
    megan_busy = {
        "Monday": [(parse_time("13:00"), parse_time("13:30")),
                   (parse_time("14:00"), parse_time("15:30"))],
        "Tuesday": [(parse_time("9:00"), parse_time("9:30")),
                    (parse_time("12:00"), parse_time("12:30")),
                    (parse_time("16:00"), parse_time("17:00"))],
        "Wednesday": [(parse_time("9:30"), parse_time("10:00")),
                       (parse_time("10:30"), parse_time("11:30")),
                       (parse_time("12:30"), parse_time("14:00")),
                       (parse_time("16:00"), parse_time("16:30"))],
        "Thursday": [(parse_time("13:30"), parse_time("14:30")),
                     (parse_time("15:00"), parse_time("15:30"))]
    }
    
    daniel_busy = {
        "Monday": [(parse_time("10:00"), parse_time("11:30")),
                   (parse_time("12:30"), parse_time("15:00"))],
        "Tuesday": [(parse_time("9:00"), parse_time("10:00")),
                    (parse_time("10:30"), parse_time("17:00"))],
        "Wednesday": [(parse_time("9:00"), parse_time("10:00")),
                       (parse_time("10:30"), parse_time("11:30")),
                       (parse_time("12:00"), parse_time("17:00"))],
        "Thursday": [(parse_time("9:00"), parse_time("12:00")),
                     (parse_time("12:30"), parse_time("14:30")),
                     (parse_time("15:00"), parse_time("15:30")),
                     (parse_time("16:00"), parse_time("17:00"))]
    }
    
    participants = [megan_busy, daniel_busy]
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    meeting_duration = 60  # 1 hour
    
    day, time_range = find_earliest_meeting_slot(participants, days, meeting_duration)
    start_time, end_time = time_range.split('-')
    print(f"{day}: {start_time}-{end_time}")

if __name__ == "__main__":
    main()