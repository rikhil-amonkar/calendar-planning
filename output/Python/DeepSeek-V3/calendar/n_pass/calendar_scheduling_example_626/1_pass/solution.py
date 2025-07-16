from typing import List, Dict, Tuple

def parse_time(time_str: str) -> int:
    """Convert time string in HH:MM format to minutes since 9:00."""
    hours, minutes = map(int, time_str.split(':'))
    return (hours - 9) * 60 + minutes

def format_time(minutes: int) -> str:
    """Convert minutes since 9:00 back to HH:MM format."""
    hours = 9 + minutes // 60
    minutes = minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def find_meeting_slot(
    participants: List[Dict[str, List[Tuple[str, str]]]],
    days: List[str],
    work_hours: Tuple[str, str],
    duration: int
) -> Tuple[str, str]:
    """Find a meeting slot that works for all participants."""
    work_start = parse_time(work_hours[0])
    work_end = parse_time(work_hours[1])
    
    for day in days:
        # Initialize free slots for the day (work hours)
        free_slots = [(work_start, work_end)]
        
        # Process each participant's schedule for the day
        for participant in participants:
            day_schedule = participant.get(day, [])
            new_free_slots = []
            
            for slot_start, slot_end in free_slots:
                current_start = slot_start
                
                # Sort meetings by start time
                day_schedule_sorted = sorted(day_schedule, key=lambda x: parse_time(x[0]))
                
                for meeting_start, meeting_end in day_schedule_sorted:
                    meeting_start_min = parse_time(meeting_start)
                    meeting_end_min = parse_time(meeting_end)
                    
                    if current_start < meeting_start_min:
                        new_free_slots.append((current_start, meeting_start_min))
                    
                    current_start = max(current_start, meeting_end_min)
                
                if current_start < slot_end:
                    new_free_slots.append((current_start, slot_end))
            
            free_slots = new_free_slots
        
        # Find a slot that fits the duration
        for slot_start, slot_end in free_slots:
            if slot_end - slot_start >= duration:
                meeting_start = format_time(slot_start)
                meeting_end = format_time(slot_start + duration)
                return day, f"{meeting_start}:{meeting_end}"
    
    return None, None

def main():
    # Define participants' schedules
    patricia_schedule = {
        "Monday": [
            ("10:00", "10:30"),
            ("11:30", "12:00"),
            ("13:00", "13:30"),
            ("14:30", "15:30"),
            ("16:00", "16:30")
        ],
        "Tuesday": [
            ("10:00", "10:30"),
            ("11:00", "12:00"),
            ("14:00", "16:00"),
            ("16:30", "17:00")
        ]
    }
    
    jesse_schedule = {
        "Monday": [
            ("9:00", "17:00")
        ],
        "Tuesday": [
            ("11:00", "11:30"),
            ("12:00", "12:30"),
            ("13:00", "14:00"),
            ("14:30", "15:00"),
            ("15:30", "17:00")
        ]
    }
    
    participants = [patricia_schedule, jesse_schedule]
    days = ["Monday", "Tuesday"]
    work_hours = ("9:00", "17:00")
    duration = 60  # minutes
    
    day, time_slot = find_meeting_slot(participants, days, work_hours, duration)
    
    if day and time_slot:
        print(f"{day}, {time_slot}")
    else:
        print("No suitable meeting time found.")

if __name__ == "__main__":
    main()