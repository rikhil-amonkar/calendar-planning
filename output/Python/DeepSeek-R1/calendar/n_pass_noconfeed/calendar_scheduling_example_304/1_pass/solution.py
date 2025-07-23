def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1]) if len(parts) > 1 else 0
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    day = "Monday"
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    duration = 30
    
    christine_busy = ["9:30-10:30", "12:00-12:30", "13:00-13:30", "14:30-15:00", "16:00-16:30"]
    bobby_busy = ["12:00-12:30", "14:30-15:00"]
    elizabeth_busy = ["9:00-9:30", "11:30-13:00", "13:30-14:00", "15:00-15:30", "16:00-17:00"]
    tyler_busy = ["9:00-11:00", "12:00-12:30", "13:00-13:30", "15:30-16:00", "16:30-17:00"]
    edward_busy = ["9:00-9:30", "10:00-11:00", "11:30-14:00", "14:30-15:30", "16:00-17:00"]
    
    all_busy = []
    
    def add_busy_intervals(busy_list):
        for interval in busy_list:
            start_str, end_str = interval.split('-')
            start_min = time_to_minutes(start_str)
            end_min = time_to_minutes(end_str)
            all_busy.append((start_min, end_min))
    
    add_busy_intervals(christine_busy)
    add_busy_intervals(bobby_busy)
    add_busy_intervals(elizabeth_busy)
    add_busy_intervals(tyler_busy)
    add_busy_intervals(edward_busy)
    
    if not all_busy:
        merged_busy = []
    else:
        all_busy.sort(key=lambda x: x[0])
        merged_busy = []
        current_start, current_end = all_busy[0]
        for i in range(1, len(all_busy)):
            s, e = all_busy[i]
            if s <= current_end:
                if e > current_end:
                    current_end = e
            else:
                merged_busy.append((current_start, current_end))
                current_start, current_end = s, e
        merged_busy.append((current_start, current_end))
    
    free_intervals = []
    current = work_start
    for start, end in merged_busy:
        if start > current:
            free_intervals.append((current, start))
        current = max(current, end)
    if current < work_end:
        free_intervals.append((current, work_end))
    
    valid_slots = []
    for start, end in free_intervals:
        if end - start >= duration:
            valid_slots.append((start, end))
    
    preferred_slots = []
    other_slots = []
    preference_cutoff = time_to_minutes("13:00")  # 780 minutes
    for slot in valid_slots:
        s, e = slot
        if e <= preference_cutoff:
            preferred_slots.append(slot)
        else:
            other_slots.append(slot)
    
    if preferred_slots:
        chosen_slot = preferred_slots[0]
    elif other_slots:
        chosen_slot = other_slots[0]
    else:
        chosen_slot = None
    
    if chosen_slot:
        start_min, end_min = chosen_slot
        start_time = minutes_to_time(start_min)
        end_time = minutes_to_time(end_min)
        time_str = f"{start_time}:{end_time}"
        print(day)
        print(time_str)
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()