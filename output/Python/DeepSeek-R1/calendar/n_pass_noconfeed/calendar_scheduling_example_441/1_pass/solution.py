def main():
    # Work hours: 9:00 to 17:00 (converted to minutes from 9:00 base)
    work_start = 0      # 9:00 in minutes from base (0 minutes)
    work_end = 480      # 17:00 (8 hours * 60 minutes = 480)
    duration = 30       # meeting duration in minutes
    
    # Convert time string to minutes since 9:00
    def time_to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return (h - 9) * 60 + m

    # Participant schedules with their busy intervals (converted to minutes)
    schedules = {
        'Joan': [('11:30', '12:00'), ('14:30', '15:00')],
        'Megan': [('9:00', '10:00'), ('14:00', '14:30'), ('16:00', '16:30')],
        'Austin': [],
        'Betty': [('9:30', '10:00'), ('11:30', '12:00'), ('13:30', '14:00'), ('16:00', '16:30')],
        'Judith': [('9:00', '11:00'), ('12:00', '13:00'), ('14:00', '15:00')],
        'Terry': [('9:30', '10:00'), ('11:30', '12:30'), ('13:00', '14:00'), ('15:00', '15:30'), ('16:00', '17:00')],
        'Kathryn': [('9:30', '10:00'), ('10:30', '11:00'), ('11:30', '13:00'), ('14:00', '16:00'), ('16:30', '17:00')]
    }
    
    # Convert all busy intervals to minutes
    for person, intervals in schedules.items():
        converted = []
        for start_str, end_str in intervals:
            start_min = time_to_minutes(start_str)
            end_min = time_to_minutes(end_str)
            converted.append((start_min, end_min))
        schedules[person] = converted

    # Generate candidate slots (every 30 minutes from work_start to work_end - duration)
    candidate_slots = range(work_start, work_end - duration + 1, 30)
    found_slot = None
    
    # Check each candidate slot
    for slot_start in candidate_slots:
        slot_end = slot_start + duration
        slot_available = True
        
        # Check availability for each participant
        for busy_intervals in schedules.values():
            if not slot_available:
                break
            for busy_start, busy_end in busy_intervals:
                # Check overlap: [slot_start, slot_end) and [busy_start, busy_end)
                if slot_start < busy_end and slot_end > busy_start:
                    slot_available = False
                    break
        
        if slot_available:
            found_slot = (slot_start, slot_end)
            break
    
    # Convert found slot back to time string
    if found_slot:
        s, e = found_slot
        start_hour = 9 + s // 60
        start_min = s % 60
        end_hour = 9 + e // 60
        end_min = e % 60
        
        # Format the time string as HH:MM:HH:MM
        time_str = f"{start_hour}:{start_min:02d}:{end_hour}:{end_min:02d}"
        print("Monday")
        print(time_str)
    else:
        # According to the problem, a solution exists, so this should not happen
        print("No suitable slot found")

if __name__ == "__main__":
    main()