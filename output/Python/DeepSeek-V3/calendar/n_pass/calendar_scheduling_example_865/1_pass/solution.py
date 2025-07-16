from typing import List, Dict, Tuple

def parse_time(time_str: str) -> int:
    """Convert time string in HH:MM format to minutes since 9:00."""
    hh, mm = map(int, time_str.split(':'))
    return (hh - 9) * 60 + mm

def format_time(minutes: int) -> str:
    """Convert minutes since 9:00 back to HH:MM format."""
    hh = 9 + minutes // 60
    mm = minutes % 60
    return f"{hh:02d}:{mm:02d}"

def find_earliest_meeting_time(
    participants: List[Dict[str, List[Tuple[int, int]]]],
    days: List[str],
    duration: int,
    work_start: str = "9:00",
    work_end: str = "17:00"
) -> Tuple[str, str]:
    """Find the earliest available meeting time for all participants."""
    work_start_min = parse_time(work_start)
    work_end_min = parse_time(work_end)
    total_slots = work_end_min - work_start_min
    
    for day_idx, day in enumerate(days):
        # Initialize a list to track availability for each minute (True means available)
        availability = [True] * total_slots
        
        for participant in participants:
            # Get the participant's busy slots for the current day
            busy_slots = participant.get(day, [])
            for start, end in busy_slots:
                # Mark the busy slots as unavailable
                for minute in range(start, end):
                    if minute < work_start_min or minute >= work_end_min:
                        continue  # Outside work hours
                    idx = minute - work_start_min
                    if idx < len(availability):
                        availability[idx] = False
        
        # Find the earliest available slot of the required duration
        consecutive = 0
        for minute in range(total_slots):
            if availability[minute]:
                consecutive += 1
                if consecutive >= duration:
                    start_minute = minute - duration + 1
                    start_time = start_minute + work_start_min
                    end_time = start_time + duration
                    return day, f"{format_time(start_time)}:{format_time(end_time)}"
            else:
                consecutive = 0
    return None, None

def main():
    # Define work hours and meeting duration
    work_start = "9:00"
    work_end = "17:00"
    duration = 60  # minutes
    
    # Define days to consider
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    
    # Parse participants' schedules into minutes since 9:00
    megan_schedule = {
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
    
    daniel_schedule = {
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
    
    participants = [megan_schedule, daniel_schedule]
    
    day, time_range = find_earliest_meeting_time(participants, days, duration, work_start, work_end)
    
    if day and time_range:
        print(f"{day}: {time_range}")
    else:
        print("No suitable meeting time found.")

if __name__ == "__main__":
    main()