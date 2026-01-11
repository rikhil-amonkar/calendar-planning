def time_to_minutes(t):
    # t is "HH:MM"
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def add_busy(day_busy, start_str, end_str):
    start_min = time_to_minutes(start_str)
    end_min = time_to_minutes(end_str)
    day_busy.append((start_min, end_min))

def is_free(day_busy, slot_start, slot_end):
    for bs, be in day_busy:
        if not (slot_end <= bs or slot_start >= be):
            return False
    return True

def find_earliest_slot(days, mary_busy, alexis_busy, duration_min=30, work_start="9:00", work_end="17:00"):
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    
    for day in days:
        mary_day = mary_busy.get(day, [])
        alexis_day = alexis_busy.get(day, [])
        
        slot_start = work_start_min
        while slot_start + duration_min <= work_end_min:
            slot_end = slot_start + duration_min
            if is_free(mary_day, slot_start, slot_end) and is_free(alexis_day, slot_start, slot_end):
                return day, slot_start, slot_end
            slot_start += 30  # check every 30 minutes
    return None

def main():
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    
    # Mary's schedule
    mary_busy = {
        "Tuesday": [(time_to_minutes("10:00"), time_to_minutes("10:30")),
                    (time_to_minutes("15:30"), time_to_minutes("16:00"))],
        "Wednesday": [(time_to_minutes("9:30"), time_to_minutes("10:00")),
                      (time_to_minutes("15:00"), time_to_minutes("15:30"))],
        "Thursday": [(time_to_minutes("9:00"), time_to_minutes("10:00")),
                     (time_to_minutes("10:30"), time_to_minutes("11:30"))]
    }
    
    # Alexis's schedule
    alexis_busy = {
        "Monday": [(time_to_minutes("9:00"), time_to_minutes("10:00")),
                   (time_to_minutes("10:30"), time_to_minutes("12:00")),
                   (time_to_minutes("12:30"), time_to_minutes("16:30"))],
        "Tuesday": [(time_to_minutes("9:00"), time_to_minutes("10:00")),
                    (time_to_minutes("10:30"), time_to_minutes("11:30")),
                    (time_to_minutes("12:00"), time_to_minutes("15:30")),
                    (time_to_minutes("16:00"), time_to_minutes("17:00"))],
        "Wednesday": [(time_to_minutes("9:00"), time_to_minutes("11:00")),
                      (time_to_minutes("11:30"), time_to_minutes("17:00"))],
        "Thursday": [(time_to_minutes("10:00"), time_to_minutes("12:00")),
                     (time_to_minutes("14:00"), time_to_minutes("14:30")),
                     (time_to_minutes("15:30"), time_to_minutes("16:00")),
                     (time_to_minutes("16:30"), time_to_minutes("17:00"))]
    }
    
    result = find_earliest_slot(days, mary_busy, alexis_busy, 30, "9:00", "17:00")
    
    if result:
        day, start_min, end_min = result
        start_str = minutes_to_time(start_min)
        end_str = minutes_to_time(end_min)
        print(f"{day} {start_str}:{end_str}")
    else:
        print("No slot found")

if __name__ == "__main__":
    main()