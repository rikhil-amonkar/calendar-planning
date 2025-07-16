def main():
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    work_start = 540   # 9:00 in minutes from midnight
    work_end = 1020    # 17:00
    slot_duration = 30  # meeting duration

    # Generate time slots for one day: from 9:00 to 16:30 (inclusive)
    slots = []
    current = work_start
    while current <= work_end - slot_duration:
        slots.append(current)
        current += slot_duration

    # Predefined busy intervals for Mary and Alexis (in minutes)
    mary_busy = {
        'Monday': [],
        'Tuesday': [(600, 630), (930, 960)],      # 10:00-10:30, 15:30-16:00
        'Wednesday': [(570, 600), (900, 930)],    # 9:30-10:00, 15:00-15:30
        'Thursday': [(540, 600), (630, 690)]      # 9:00-10:00, 10:30-11:30
    }

    alexis_busy = {
        'Monday': [(540, 600), (630, 720), (750, 990)],      # 9:00-10:00, 10:30-12:00, 12:30-16:30
        'Tuesday': [(540, 600), (630, 690), (720, 930), (960, 1020)], # 9:00-10:00, 10:30-11:30, 12:00-15:30, 16:00-17:00
        'Wednesday': [(540, 660), (690, 1020)],               # 9:00-11:00, 11:30-17:00
        'Thursday': [(600, 720), (840, 870), (930, 960), (990, 1020)] # 10:00-12:00, 14:00-14:30, 15:30-16:00, 16:30-17:00
    }

    # Iterate over days in order
    for day in days:
        # Initialize free slots for Mary and Alexis as all True
        free_mary = [True] * len(slots)
        free_alexis = [True] * len(slots)
        
        # Mark Mary's busy slots for this day
        for (busy_start, busy_end) in mary_busy[day]:
            for idx, slot_start in enumerate(slots):
                slot_end = slot_start + slot_duration
                # Check for overlap: [slot_start, slot_end) and [busy_start, busy_end)
                if slot_start < busy_end and slot_end > busy_start:
                    free_mary[idx] = False
                    
        # Mark Alexis's busy slots for this day
        for (busy_start, busy_end) in alexis_busy[day]:
            for idx, slot_start in enumerate(slots):
                slot_end = slot_start + slot_duration
                if slot_start < busy_end and slot_end > busy_start:
                    free_alexis[idx] = False
                    
        # Find the first free slot for both
        for idx in range(len(slots)):
            if free_mary[idx] and free_alexis[idx]:
                start_min = slots[idx]
                end_min = start_min + slot_duration
                
                # Convert start time to HH:MM
                start_hour = start_min // 60
                start_minute = start_min % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                
                # Convert end time to HH:MM
                end_hour = end_min // 60
                end_minute = end_min % 60
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                
                # Format time range as HH:MM:HH:MM
                time_range = f"{start_str}:{end_str}"
                
                # Output day and time range
                print(day)
                print(time_range)
                return
                
    # If no slot found (though guaranteed), output a fallback
    print("No slot found")

if __name__ == "__main__":
    main()