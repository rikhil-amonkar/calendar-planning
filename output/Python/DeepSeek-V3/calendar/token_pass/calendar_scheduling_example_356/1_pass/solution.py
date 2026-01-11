def time_to_minutes(t):
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def main():
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    duration = 30
    
    # Busy intervals in minutes from midnight, but we'll convert from 9:00 later
    # Actually easier: convert all to minutes from 0:00, then subtract work_start for offset if needed.
    # But simpler: just work in minutes from 9:00.
    
    # Schedules as (start, end) in minutes from 9:00
    katherine = [(180, 210), (240, 330)]
    rebecca = []
    julie = [(0, 30), (90, 120), (270, 300), (360, 390)]
    angela = [(0, 60), (90, 120), (150, 300), (330, 360), (450, 480)]
    nicholas = [(30, 120), (150, 270), (300, 420), (450, 480)]
    carl = [(0, 120), (150, 210), (240, 330), (360, 420), (450, 480)]
    
    all_schedules = [katherine, rebecca, julie, angela, nicholas, carl]
    
    # Find free slots for all
    possible_slots = []
    
    for start in range(work_start, work_end - duration + 1, 5):  # check every 5 minutes for accuracy
        end = start + duration
        if end > work_end:
            break
        ok = True
        for schedule in all_schedules:
            for busy_start, busy_end in schedule:
                if not (end <= busy_start or start >= busy_end):
                    ok = False
                    break
            if not ok:
                break
        if ok:
            possible_slots.append((start, end))
    
    # Filter by Angela's preference (after 15:00)
    preferred_slots = [slot for slot in possible_slots if slot[0] >= time_to_minutes("15:00") - work_start]
    
    # Choose the earliest preferred slot
    if preferred_slots:
        chosen = preferred_slots[0]
    elif possible_slots:
        chosen = possible_slots[0]
    else:
        print("No slot found")
        return
    
    # Convert back to HH:MM format from 9:00 offset
    def offset_to_time(offset):
        total_minutes = work_start + offset
        h = total_minutes // 60
        m = total_minutes % 60
        return f"{h:02d}:{m:02d}"
    
    start_time = offset_to_time(chosen[0])
    end_time = offset_to_time(chosen[1])
    
    print(f"Monday {start_time}:{end_time}")

if __name__ == "__main__":
    main()