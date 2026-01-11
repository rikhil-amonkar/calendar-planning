def time_to_minutes(t):
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def find_slot(work_start, work_end, busy, duration):
    # busy is list of (start, end) in minutes
    # sort busy intervals
    busy = sorted(busy, key=lambda x: x[0])
    
    # check from work_start to first busy
    if busy and work_start + duration <= busy[0][0]:
        return work_start, work_start + duration
    
    # check between busy intervals
    for i in range(len(busy) - 1):
        if busy[i][1] + duration <= busy[i + 1][0]:
            return busy[i][1], busy[i][1] + duration
    
    # check after last busy
    if busy and busy[-1][1] + duration <= work_end:
        return busy[-1][1], busy[-1][1] + duration
    
    # if no busy intervals at all
    if not busy and work_start + duration <= work_end:
        return work_start, work_start + duration
    
    return None

def main():
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    duration = 30  # minutes
    
    # Samuel's busy times in minutes
    busy_by_day = {
        "Monday": [
            (time_to_minutes("10:30"), time_to_minutes("11:00")),
            (time_to_minutes("12:00"), time_to_minutes("12:30")),
            (time_to_minutes("13:00"), time_to_minutes("15:00")),
            (time_to_minutes("15:30"), time_to_minutes("16:30"))
        ],
        "Tuesday": [
            (time_to_minutes("9:00"), time_to_minutes("12:00")),
            (time_to_minutes("14:00"), time_to_minutes("15:30")),
            (time_to_minutes("16:30"), time_to_minutes("17:00"))
        ],
        "Wednesday": [
            (time_to_minutes("10:30"), time_to_minutes("11:00")),
            (time_to_minutes("11:30"), time_to_minutes("12:00")),
            (time_to_minutes("12:30"), time_to_minutes("13:00")),
            (time_to_minutes("14:00"), time_to_minutes("14:30")),
            (time_to_minutes("15:00"), time_to_minutes("16:00"))
        ]
    }
    
    # Day preference order: Monday, Tuesday, Wednesday
    days = ["Monday", "Tuesday", "Wednesday"]
    
    for day in days:
        slot = find_slot(work_start, work_end, busy_by_day[day], duration)
        if slot:
            start_min, end_min = slot
            start_time = minutes_to_time(start_min)
            end_time = minutes_to_time(end_min)
            print(f"{day}:{start_time}:{end_time}")
            return
    
    print("No suitable slot found")

if __name__ == "__main__":
    main()