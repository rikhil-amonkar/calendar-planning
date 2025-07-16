from typing import List, Dict, Tuple

def schedule_meeting(participants: List[Dict], days: List[str], work_hours: Tuple[str, str], duration: int) -> Tuple[str, str]:
    # Parse work hours
    work_start, work_end = work_hours
    work_start_min = convert_time_to_minutes(work_start)
    work_end_min = convert_time_to_minutes(work_end)
    
    # Iterate through each day
    for day in days:
        # Check Betty's constraints
        if day == "Monday":
            continue
        if day == "Tuesday" or day == "Thursday":
            betty_min_start = convert_time_to_minutes("15:00")
        else:
            betty_min_start = work_start_min
        
        # Check Scott's preference to avoid Wednesday
        if day == "Wednesday":
            continue
        
        # Get busy times for both participants on this day
        betty_busy = [busy for busy in participants[0]['busy'] if busy['day'] == day]
        scott_busy = [busy for busy in participants[1]['busy'] if busy['day'] == day]
        
        # Merge and sort all busy times
        all_busy = []
        for busy in betty_busy:
            all_busy.append((convert_time_to_minutes(busy['start']), convert_time_to_minutes(busy['end'])))
        for busy in scott_busy:
            all_busy.append((convert_time_to_minutes(busy['start']), convert_time_to_minutes(busy['end'])))
        all_busy.sort()
        
        # Find available slots
        available_slots = []
        prev_end = max(work_start_min, betty_min_start)
        
        for start, end in all_busy:
            if start > prev_end:
                available_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        
        if work_end_min > prev_end:
            available_slots.append((prev_end, work_end_min))
        
        # Check for a slot that fits the duration
        for slot_start, slot_end in available_slots:
            if slot_end - slot_start >= duration:
                meeting_start = slot_start
                meeting_end = meeting_start + duration
                return day, f"{convert_minutes_to_time(meeting_start)}:{convert_minutes_to_time(meeting_end)}"
    
    return None, None

def convert_time_to_minutes(time_str: str) -> int:
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def convert_minutes_to_time(minutes: int) -> str:
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define participants' busy times
betty_busy = [
    {'day': 'Monday', 'start': '10:00', 'end': '10:30'},
    {'day': 'Monday', 'start': '13:30', 'end': '14:00'},
    {'day': 'Monday', 'start': '15:00', 'end': '15:30'},
    {'day': 'Monday', 'start': '16:00', 'end': '16:30'},
    {'day': 'Tuesday', 'start': '9:00', 'end': '9:30'},
    {'day': 'Tuesday', 'start': '11:30', 'end': '12:00'},
    {'day': 'Tuesday', 'start': '12:30', 'end': '13:00'},
    {'day': 'Tuesday', 'start': '13:30', 'end': '14:00'},
    {'day': 'Tuesday', 'start': '16:30', 'end': '17:00'},
    {'day': 'Wednesday', 'start': '9:30', 'end': '10:30'},
    {'day': 'Wednesday', 'start': '13:00', 'end': '13:30'},
    {'day': 'Wednesday', 'start': '14:00', 'end': '14:30'},
    {'day': 'Thursday', 'start': '9:30', 'end': '10:00'},
    {'day': 'Thursday', 'start': '11:30', 'end': '12:00'},
    {'day': 'Thursday', 'start': '14:00', 'end': '14:30'},
    {'day': 'Thursday', 'start': '15:00', 'end': '15:30'},
    {'day': 'Thursday', 'start': '16:30', 'end': '17:00'}
]

scott_busy = [
    {'day': 'Monday', 'start': '9:30', 'end': '15:00'},
    {'day': 'Monday', 'start': '15:30', 'end': '16:00'},
    {'day': 'Monday', 'start': '16:30', 'end': '17:00'},
    {'day': 'Tuesday', 'start': '9:00', 'end': '9:30'},
    {'day': 'Tuesday', 'start': '10:00', 'end': '11:00'},
    {'day': 'Tuesday', 'start': '11:30', 'end': '12:00'},
    {'day': 'Tuesday', 'start': '12:30', 'end': '13:30'},
    {'day': 'Tuesday', 'start': '14:00', 'end': '15:00'},
    {'day': 'Tuesday', 'start': '16:00', 'end': '16:30'},
    {'day': 'Wednesday', 'start': '9:30', 'end': '12:30'},
    {'day': 'Wednesday', 'start': '13:00', 'end': '13:30'},
    {'day': 'Wednesday', 'start': '14:00', 'end': '14:30'},
    {'day': 'Wednesday', 'start': '15:00', 'end': '15:30'},
    {'day': 'Wednesday', 'start': '16:00', 'end': '16:30'},
    {'day': 'Thursday', 'start': '9:00', 'end': '9:30'},
    {'day': 'Thursday', 'start': '10:00', 'end': '10:30'},
    {'day': 'Thursday', 'start': '11:00', 'end': '12:00'},
    {'day': 'Thursday', 'start': '12:30', 'end': '13:00'},
    {'day': 'Thursday', 'start': '15:00', 'end': '16:00'},
    {'day': 'Thursday', 'start': '16:30', 'end': '17:00'}
]

participants = [
    {'name': 'Betty', 'busy': betty_busy},
    {'name': 'Scott', 'busy': scott_busy}
]

days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
work_hours = ('9:00', '17:00')
duration = 30  # minutes

day, time_range = schedule_meeting(participants, days, work_hours, duration)
if day and time_range:
    print(f"{day}: {time_range}")
else:
    print("No suitable time found.")