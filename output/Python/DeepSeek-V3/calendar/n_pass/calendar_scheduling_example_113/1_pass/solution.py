def find_meeting_time(participants_schedules, meeting_duration_minutes, work_hours_start, work_hours_end):
    # Convert all time slots to minutes since start of the day for easier calculation
    work_start = work_hours_start[0] * 60 + work_hours_start[1]
    work_end = work_hours_end[0] * 60 + work_hours_end[1]
    
    # Generate all possible time slots in the work hours
    possible_slots = []
    current_time = work_start
    while current_time + meeting_duration_minutes <= work_end:
        possible_slots.append((current_time, current_time + meeting_duration_minutes))
        current_time += 1  # Check every minute
    
    # Check each slot against all participants' schedules
    for slot in possible_slots:
        slot_start, slot_end = slot
        all_available = True
        for person_schedule in participants_schedules:
            person_available = True
            for busy_start, busy_end in person_schedule:
                busy_start_min = busy_start[0] * 60 + busy_start[1]
                busy_end_min = busy_end[0] * 60 + busy_end[1]
                # Check if slot overlaps with any busy time
                if not (slot_end <= busy_start_min or slot_start >= busy_end_min):
                    person_available = False
                    break
            if not person_available:
                all_available = False
                break
        if all_available:
            return slot
    return None

def main():
    # Define participants' schedules in (HH, MM) format
    bradley_schedule = [
        ((9, 30), (10, 0)),
        ((12, 30), (13, 0)),
        ((13, 30), (14, 0)),
        ((15, 30), (16, 0))
    ]
    teresa_schedule = [
        ((10, 30), (11, 0)),
        ((12, 0), (12, 30)),
        ((13, 0), (13, 30)),
        ((14, 30), (15, 0))
    ]
    elizabeth_schedule = [
        ((9, 0), (9, 30)),
        ((10, 30), (11, 30)),
        ((13, 0), (13, 30)),
        ((14, 30), (15, 0)),
        ((15, 30), (17, 0))
    ]
    christian_schedule = [
        ((9, 0), (9, 30)),
        ((10, 30), (17, 0))
    ]
    
    participants_schedules = [bradley_schedule, teresa_schedule, elizabeth_schedule, christian_schedule]
    meeting_duration = 30  # minutes
    work_hours_start = (9, 0)
    work_hours_end = (17, 0)
    
    meeting_slot = find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end)
    
    if meeting_slot:
        start_min, end_min = meeting_slot
        start_hh = start_min // 60
        start_mm = start_min % 60
        end_hh = end_min // 60
        end_mm = end_min % 60
        print(f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}")
        print("Monday")
    else:
        print("No suitable time found.")

if __name__ == "__main__":
    main()