def time_to_min(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def find_meeting_time(participants_busy, work_start, work_end, duration_min, days, blacklist_days):
    work_start_min = time_to_min(work_start)
    work_end_min = time_to_min(work_end)
    duration = duration_min
    
    for day in days:
        if day in blacklist_days:
            continue
        
        # Generate free slots for each participant on this day
        free_slots_all = []
        for person in participants_busy:
            busy = participants_busy[person].get(day, [])
            # Convert busy times to minutes
            busy_min = [(time_to_min(s), time_to_min(e)) for s, e in busy]
            busy_min.sort()
            
            # Start with whole work day free
            free = []
            current_start = work_start_min
            
            for bs, be in busy_min:
                if current_start < bs:
                    free.append((current_start, bs))
                current_start = max(current_start, be)
            if current_start < work_end_min:
                free.append((current_start, work_end_min))
            
            free_slots_all.append(free)
        
        # Intersect free slots
        if not free_slots_all:
            continue
        
        intersected = free_slots_all[0]
        for free_slots in free_slots_all[1:]:
            new_intersected = []
            i = j = 0
            while i < len(intersected) and j < len(free_slots):
                s1, e1 = intersected[i]
                s2, e2 = free_slots[j]
                start_max = max(s1, s2)
                end_min = min(e1, e2)
                if start_max < end_min:
                    new_intersected.append((start_max, end_min))
                if e1 < e2:
                    i += 1
                else:
                    j += 1
            intersected = new_intersected
        
        # Check for a slot long enough
        for s, e in intersected:
            if e - s >= duration:
                return day, min_to_time(s), min_to_time(s + duration)
    
    return None, None, None

def main():
    # Busy times in HH:MM format
    participants_busy = {
        "Cheryl": {
            "Monday": [("9:00", "9:30"), ("11:30", "13:00"), ("15:30", "16:00")],
            "Tuesday": [("15:00", "15:30")],
        },
        "Kyle": {
            "Monday": [("9:00", "17:00")],
            "Tuesday": [("9:30", "17:00")],
            "Wednesday": [("9:00", "9:30"), ("10:00", "13:00"), ("13:30", "14:00"), ("14:30", "17:00")],
        }
    }
    
    work_start = "9:00"
    work_end = "17:00"
    duration_min = 30
    days = ["Monday", "Tuesday", "Wednesday"]
    blacklist_days = {"Wednesday"}  # Cheryl cannot meet Wednesday
    
    day, start, end = find_meeting_time(participants_busy, work_start, work_end, duration_min, days, blacklist_days)
    
    if day:
        print(f"{day}:{start}:{end}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()