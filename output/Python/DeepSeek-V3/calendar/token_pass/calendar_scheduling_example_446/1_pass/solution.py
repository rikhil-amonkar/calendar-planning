from datetime import datetime, timedelta

def schedule_meeting():
    # Define work hours
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    meeting_duration = timedelta(minutes=30)
    
    # Busy times for each person (as list of (start, end) datetime tuples)
    # Megan
    megan_busy = [
        ("09:00", "09:30"),
        ("10:00", "11:00"),
        ("12:00", "12:30")
    ]
    
    # Christine
    christine_busy = [
        ("09:00", "09:30"),
        ("11:30", "12:00"),
        ("13:00", "14:00"),
        ("15:30", "16:30")
    ]
    
    # Gabriel - free all day
    gabriel_busy = []
    
    # Sara
    sara_busy = [
        ("11:30", "12:00"),
        ("14:30", "15:00")
    ]
    
    # Bruce
    bruce_busy = [
        ("09:30", "10:00"),
        ("10:30", "12:00"),
        ("12:30", "14:00"),
        ("14:30", "15:00"),
        ("15:30", "16:30")
    ]
    
    # Kathryn
    kathryn_busy = [
        ("10:00", "15:30"),
        ("16:00", "16:30")
    ]
    
    # Billy
    billy_busy = [
        ("09:00", "09:30"),
        ("11:00", "11:30"),
        ("12:00", "14:00"),
        ("14:30", "15:30")
    ]
    
    # Combine all busy times
    all_busy = []
    for busy_list in [megan_busy, christine_busy, gabriel_busy, sara_busy, 
                      bruce_busy, kathryn_busy, billy_busy]:
        for start_str, end_str in busy_list:
            start_time = datetime.strptime(start_str, "%H:%M")
            end_time = datetime.strptime(end_str, "%H:%M")
            all_busy.append((start_time, end_time))
    
    # Sort busy times by start
    all_busy.sort(key=lambda x: x[0])
    
    # Merge overlapping busy intervals
    merged_busy = []
    for start, end in all_busy:
        if not merged_busy:
            merged_busy.append([start, end])
        else:
            last_start, last_end = merged_busy[-1]
            if start <= last_end:
                merged_busy[-1][1] = max(last_end, end)
            else:
                merged_busy.append([start, end])
    
    # Find free slots
    current_time = work_start
    free_slots = []
    
    for busy_start, busy_end in merged_busy:
        if current_time < busy_start:
            free_end = min(busy_start, work_end)
            if free_end - current_time >= meeting_duration:
                free_slots.append((current_time, free_end))
        current_time = max(current_time, busy_end)
    
    # Check after last busy period
    if current_time < work_end:
        if work_end - current_time >= meeting_duration:
            free_slots.append((current_time, work_end))
    
    # Find first suitable slot
    for slot_start, slot_end in free_slots:
        slot_duration = slot_end - slot_start
        if slot_duration >= meeting_duration:
            # We can start at slot_start
            meeting_start = slot_start
            meeting_end = meeting_start + meeting_duration
            
            # Check if this slot works for everyone
            works_for_all = True
            
            # Check against each person's schedule
            persons_busy = [megan_busy, christine_busy, gabriel_busy, sara_busy,
                           bruce_busy, kathryn_busy, billy_busy]
            
            for person_busy in persons_busy:
                for busy_start_str, busy_end_str in person_busy:
                    busy_start = datetime.strptime(busy_start_str, "%H:%M")
                    busy_end = datetime.strptime(busy_end_str, "%H:%M")
                    
                    # Check for overlap
                    if not (meeting_end <= busy_start or meeting_start >= busy_end):
                        works_for_all = False
                        break
                if not works_for_all:
                    break
            
            if works_for_all:
                # Format output
                start_str = meeting_start.strftime("%H:%M")
                end_str = meeting_end.strftime("%H:%M")
                return f"Monday {start_str}:{end_str}"
    
    return "No suitable time found"

if __name__ == "__main__":
    result = schedule_meeting()
    print(result)