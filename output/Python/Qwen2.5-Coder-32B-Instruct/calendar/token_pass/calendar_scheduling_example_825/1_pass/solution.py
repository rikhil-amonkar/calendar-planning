from datetime import datetime, timedelta

def parse_schedule(schedule_str):
    """Converts a string of busy times into a list of tuples."""
    return [tuple(map(int, t.split(':'))) for t in schedule_str.split(', ')]

def find_free_slots(busy_times, start_hour=9, end_hour=17):
    """Finds free slots in a day given busy times."""
    busy_times.sort()
    current_time = start_hour * 60
    free_slots = []
    
    for start, end in busy_times:
        if current_time < start * 60:
            free_slots.append((current_time // 60, current_time % 60, start))
        current_time = max(current_time, end * 60)
    
    if current_time < end_hour * 60:
        free_slots.append((current_time // 60, current_time % 60, end_hour))
    
    return [(h, m, e) for h, m, e in free_slots if (e - h) >= 1]

def find_common_free_slot(laura_busy, philip_busy, start_hour=9, end_hour=17):
    """Finds a common free slot of at least one hour between two people."""
    laura_slots = find_free_slots(laura_busy, start_hour, end_hour)
    philip_slots = find_free_slots(philip_busy, start_hour, end_hour)
    
    i, j = 0, 0
    while i < len(laura_slots) and j < len(philip_slots):
        laura_start, laura_min, laura_end = laura_slots[i]
        philip_start, philip_min, philip_end = philip_slots[j]
        
        # Calculate overlap
        start_overlap = max(laura_start * 60 + laura_min, philip_start * 60 + philip_min)
        end_overlap = min(laura_end * 60, philip_end * 60)
        
        if start_overlap < end_overlap and (end_overlap - start_overlap) >= 60:
            # Found a common free slot of at least one hour
            return (start_overlap // 60, start_overlap % 60, end_overlap // 60, end_overlap % 60)
        
        # Move to the next slot that ends earlier
        if laura_end <= philip_end:
            i += 1
        else:
            j += 1
    
    return None

def main():
    laura_schedule = {
        'Monday': '10:30, 12:30, 14:30, 16:00',
        'Tuesday': '9:30, 11:00, 13:00, 14:30, 16:00',
        'Wednesday': '11:30, 12:30, 15:30',
        'Thursday': '10:30, 12:00, 15:00, 16:00'
    }
    
    philip_schedule = {
        'Monday': '9:00, 17:00',
        'Tuesday': '9:00, 11:00, 11:30, 13:00, 14:00, 15:00',
        'Wednesday': '9:00, 10:00, 11:00, 12:30, 16:00, 16:30, 17:00',
        'Thursday': '9:00, 10:30, 11:00, 12:30, 13:00, 17:00'
    }
    
    days_to_check = ['Monday', 'Tuesday', 'Thursday']
    
    for day in days_to_check:
        laura_busy = parse_schedule(laura_schedule[day])
        philip_busy = parse_schedule(philip_schedule[day])
        
        slot = find_common_free_slot(laura_busy, philip_busy)
        if slot:
            start_h, start_m, end_h, end_m = slot
            print(f"{start_h:02}:{start_m:02}:{end_h:02}:{end_m:02} {day}")
            return
    
    print("No available slot found.")

main()