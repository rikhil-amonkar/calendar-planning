from typing import List, Dict, Tuple

def parse_time(time_str: str) -> int:
    """Convert time string in format HH:MM to minutes since midnight."""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def format_time(minutes: int) -> str:
    """Convert minutes since midnight to time string in format HH:MM."""
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def find_available_slot(
    participants: List[Dict[str, List[Tuple[int, int]]]],
    work_hours: Tuple[int, int],
    duration: int,
    days: List[str],
    constraints: Dict[str, List[str]] = None
) -> Tuple[str, Tuple[int, int]]:
    """
    Find an available meeting slot that fits all participants' schedules.
    
    Args:
        participants: List of participants' busy slots per day in minutes.
        work_hours: Tuple of (start, end) in minutes.
        duration: Meeting duration in minutes.
        days: List of days to consider.
        constraints: Optional constraints per participant (e.g., cannot meet on certain days).
    
    Returns:
        Tuple of (day, (start, end)) in minutes if found, else (None, None).
    """
    if constraints is None:
        constraints = {}
    
    for day_idx, day in enumerate(days):
        # Check if day is constrained for any participant
        skip_day = False
        for participant in participants:
            name = participant.get('name', '')
            if name in constraints and day in constraints[name]:
                skip_day = True
                break
        if skip_day:
            continue
        
        # Collect all busy slots for the day
        busy_slots = []
        for participant in participants:
            busy_slots.extend(participant['busy_slots'][day_idx])
        
        # Sort and merge overlapping busy slots
        busy_slots.sort()
        merged = []
        for start, end in busy_slots:
            if not merged:
                merged.append([start, end])
            else:
                last_start, last_end = merged[-1]
                if start <= last_end:
                    merged[-1][1] = max(end, last_end)
                else:
                    merged.append([start, end])
        
        # Find available slots between work hours
        prev_end = work_hours[0]
        for start, end in merged:
            if start > prev_end and start - prev_end >= duration:
                return day, (prev_end, prev_end + duration)
            prev_end = max(prev_end, end)
        
        # Check after last busy slot
        if work_hours[1] - prev_end >= duration:
            return day, (prev_end, prev_end + duration)
    
    return None, None

def main():
    # Define work hours (9:00 to 17:00)
    work_start = parse_time("09:00")
    work_end = parse_time("17:00")
    work_hours = (work_start, work_end)
    
    # Define meeting duration (1 hour)
    duration = 60
    
    # Define days to consider
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    
    # Define participants' busy slots (in minutes since midnight)
    laura_busy = {
        "Monday": [
            (parse_time("10:30"), parse_time("11:00")),
            (parse_time("12:30"), parse_time("13:00")),
            (parse_time("14:30"), parse_time("15:30")),
            (parse_time("16:00"), parse_time("17:00"))
        ],
        "Tuesday": [
            (parse_time("09:30"), parse_time("10:00")),
            (parse_time("11:00"), parse_time("11:30")),
            (parse_time("13:00"), parse_time("13:30")),
            (parse_time("14:30"), parse_time("15:00")),
            (parse_time("16:00"), parse_time("17:00"))
        ],
        "Wednesday": [
            (parse_time("11:30"), parse_time("12:00")),
            (parse_time("12:30"), parse_time("13:00")),
            (parse_time("15:30"), parse_time("16:30"))
        ],
        "Thursday": [
            (parse_time("10:30"), parse_time("11:00")),
            (parse_time("12:00"), parse_time("13:30")),
            (parse_time("15:00"), parse_time("15:30")),
            (parse_time("16:00"), parse_time("16:30"))
        ]
    }
    
    philip_busy = {
        "Monday": [
            (parse_time("09:00"), parse_time("17:00"))
        ],
        "Tuesday": [
            (parse_time("09:00"), parse_time("11:00")),
            (parse_time("11:30"), parse_time("12:00")),
            (parse_time("13:00"), parse_time("13:30")),
            (parse_time("14:00"), parse_time("14:30")),
            (parse_time("15:00"), parse_time("16:30"))
        ],
        "Wednesday": [
            (parse_time("09:00"), parse_time("10:00")),
            (parse_time("11:00"), parse_time("12:00")),
            (parse_time("12:30"), parse_time("16:00")),
            (parse_time("16:30"), parse_time("17:00"))
        ],
        "Thursday": [
            (parse_time("09:00"), parse_time("10:30")),
            (parse_time("11:00"), parse_time("12:30")),
            (parse_time("13:00"), parse_time("17:00"))
        ]
    }
    
    # Convert busy slots to list format per day
    laura_slots = []
    philip_slots = []
    for day in days:
        laura_slots.append(laura_busy.get(day, []))
        philip_slots.append(philip_busy.get(day, []))
    
    participants = [
        {"name": "Laura", "busy_slots": laura_slots},
        {"name": "Philip", "busy_slots": philip_slots}
    ]
    
    # Define constraints (Philip cannot meet on Wednesday)
    constraints = {
        "Philip": ["Wednesday"]
    }
    
    # Find available slot
    day, (start, end) = find_available_slot(
        participants, work_hours, duration, days, constraints
    )
    
    if day:
        start_str = format_time(start)
        end_str = format_time(end)
        print(f"{day}: {start_str}:{end_str}")
    else:
        print("No available slot found.")

if __name__ == "__main__":
    main()