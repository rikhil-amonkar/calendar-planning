from datetime import datetime, timedelta

def time_to_minutes(t):
    return t.hour * 60 + t.minute

def minutes_to_time_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def add_busy_slot(busy_map, day, start_str, end_str):
    start = datetime.strptime(start_str, "%H:%M")
    end = datetime.strptime(end_str, "%H:%M")
    busy_map[day].append((time_to_minutes(start), time_to_minutes(end)))

def find_free_slots(busy_map, day, work_start_min, work_end_min, duration_min):
    busy_today = sorted(busy_map[day])
    free_slots = []
    current_time = work_start_min
    
    for start_busy, end_busy in busy_today:
        if current_time < start_busy:
            if start_busy - current_time >= duration_min:
                free_slots.append((current_time, start_busy))
        current_time = max(current_time, end_busy)
    
    if work_end_min - current_time >= duration_min:
        free_slots.append((current_time, work_end_min))
    
    return free_slots

def main():
    days = ["Monday", "Tuesday", "Wednesday"]
    work_start = time_to_minutes(datetime.strptime("9:00", "%H:%M"))
    work_end = time_to_minutes(datetime.strptime("17:00", "%H:%M"))
    duration = 30
    
    # Initialize busy maps
    amy_busy = {day: [] for day in days}
    pamela_busy = {day: [] for day in days}
    
    # Amy's busy slots
    add_busy_slot(amy_busy, "Wednesday", "11:00", "11:30")
    add_busy_slot(amy_busy, "Wednesday", "13:30", "14:00")
    
    # Pamela's busy slots
    add_busy_slot(pamela_busy, "Monday", "9:00", "10:30")
    add_busy_slot(pamela_busy, "Monday", "11:00", "16:30")
    add_busy_slot(pamela_busy, "Tuesday", "9:00", "9:30")
    add_busy_slot(pamela_busy, "Tuesday", "10:00", "17:00")
    add_busy_slot(pamela_busy, "Wednesday", "9:00", "9:30")
    add_busy_slot(pamela_busy, "Wednesday", "10:00", "11:00")
    add_busy_slot(pamela_busy, "Wednesday", "11:30", "13:30")
    add_busy_slot(pamela_busy, "Wednesday", "14:30", "15:00")
    add_busy_slot(pamela_busy, "Wednesday", "16:00", "16:30")
    
    # Preference: Pamela avoids before 16:00
    preference_start = time_to_minutes(datetime.strptime("16:00", "%H:%M"))
    
    # Find overlapping free slots
    for day in days:
        amy_free = find_free_slots(amy_busy, day, work_start, work_end, duration)
        pamela_free = find_free_slots(pamela_busy, day, work_start, work_end, duration)
        
        # Intersect free slots
        for a_start, a_end in amy_free:
            for p_start, p_end in pamela_free:
                overlap_start = max(a_start, p_start)
                overlap_end = min(a_end, p_end)
                if overlap_end - overlap_start >= duration:
                    # Check Pamela's preference: start at or after 16:00
                    if overlap_start >= preference_start:
                        # Choose the earliest possible slot in the day that meets preference
                        slot_start = overlap_start
                        slot_end = slot_start + duration
                        print(f"{day}:{minutes_to_time_str(slot_start)}:{minutes_to_time_str(slot_end)}")
                        return
    
    # If no slot after 16:00, take any slot (shouldn't happen per problem statement)
    for day in days:
        amy_free = find_free_slots(amy_busy, day, work_start, work_end, duration)
        pamela_free = find_free_slots(pamela_busy, day, work_start, work_end, duration)
        for a_start, a_end in amy_free:
            for p_start, p_end in pamela_free:
                overlap_start = max(a_start, p_start)
                overlap_end = min(a_end, p_end)
                if overlap_end - overlap_start >= duration:
                    slot_start = overlap_start
                    slot_end = slot_start + duration
                    print(f"{day}:{minutes_to_time_str(slot_start)}:{minutes_to_time_str(slot_end)}")
                    return

if __name__ == "__main__":
    main()