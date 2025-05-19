def find_meeting_time(participants_schedules, work_hours_start, work_hours_end, meeting_duration_minutes):
    # Convert work hours to minutes since midnight for easier calculation
    work_start = work_hours_start[0] * 60 + work_hours_start[1]
    work_end = work_hours_end[0] * 60 + work_hours_end[1]
    
    # Initialize the free slots as the entire work day
    free_slots = [(work_start, work_end)]
    
    # Process each participant's schedule to find common free slots
    for schedule in participants_schedules:
        busy_slots = []
        for busy in schedule:
            start = busy[0] * 60 + busy[1]
            end = busy[2] * 60 + busy[3]
            busy_slots.append((start, end))
        
        # Sort the busy slots by start time
        busy_slots.sort()
        
        # Merge overlapping or adjacent busy slots
        merged_busy = []
        for busy in busy_slots:
            if not merged_busy:
                merged_busy.append(busy)
            else:
                last_start, last_end = merged_busy[-1]
                current_start, current_end = busy
                if current_start <= last_end:
                    new_end = max(last_end, current_end)
                    merged_busy[-1] = (last_start, new_end)
                else:
                    merged_busy.append(busy)
        
        # Subtract busy slots from free slots
        new_free_slots = []
        for free_start, free_end in free_slots:
            current_free_start = free_start
            for busy_start, busy_end in merged_busy:
                if busy_start > current_free_start:
                    new_free_slots.append((current_free_start, busy_start))
                current_free_start = max(current_free_start, busy_end)
            if current_free_start < free_end:
                new_free_slots.append((current_free_start, free_end))
        free_slots = new_free_slots
    
    # Find the first free slot that can accommodate the meeting
    for slot in free_slots:
        start, end = slot
        duration = end - start
        if duration >= meeting_duration_minutes:
            meeting_start = start
            meeting_end = meeting_start + meeting_duration_minutes
            return (meeting_start, meeting_end)
    
    return None

def main():
    # Define participants' schedules in HH:MM format converted to tuples (HH, MM, HH, MM)
    participants_schedules = [
        # Stephen's busy times: 10:00-10:30, 12:00-12:30
        [(10, 0, 10, 30), (12, 0, 12, 30)],
        # Brittany's busy times: 11:00-11:30, 13:30-14:00, 15:30-16:00, 16:30-17:00
        [(11, 0, 11, 30), (13, 30, 14, 0), (15, 30, 16, 0), (16, 30, 17, 0)],
        # Dorothy's busy times: 9:00-9:30, 10:00-10:30, 11:00-12:30, 13:00-15:00, 15:30-17:00
        [(9, 0, 9, 30), (10, 0, 10, 30), (11, 0, 12, 30), (13, 0, 15, 0), (15, 30, 17, 0)],
        # Rebecca's busy times: 9:30-10:30, 11:00-11:30, 12:00-12:30, 13:00-17:00
        [(9, 30, 10, 30), (11, 0, 11, 30), (12, 0, 12, 30), (13, 0, 17, 0)],
        # Jordan's busy times: 9:00-9:30, 10:00-11:00, 11:30-12:00, 13:00-15:00, 15:30-16:30
        [(9, 0, 9, 30), (10, 0, 11, 0), (11, 30, 12, 0), (13, 0, 15, 0), (15, 30, 16, 30)]
    ]
    
    # Work hours: 9:00 to 17:00
    work_hours_start = (9, 0)
    work_hours_end = (17, 0)
    
    # Meeting duration: 30 minutes
    meeting_duration_minutes = 30
    
    # Find the meeting time
    meeting_time = find_meeting_time(participants_schedules, work_hours_start, work_hours_end, meeting_duration_minutes)
    
    if meeting_time:
        start_min, end_min = meeting_time
        start_hh = start_min // 60
        start_mm = start_min % 60
        end_hh = end_min // 60
        end_mm = end_min % 60
        print(f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}")
        print("Monday")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()