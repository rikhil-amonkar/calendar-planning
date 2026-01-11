from datetime import datetime, timedelta

def time_to_minutes(t):
    # t is string "HH:MM"
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def is_free(person_busy, day, start_min, end_min):
    # person_busy[day] is list of (start_min, end_min) busy intervals
    for s, e in person_busy.get(day, []):
        if not (end_min <= s or start_min >= e):
            return False
    return True

def main():
    # Work hours
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    duration = 30  # minutes
    
    # Joshua's busy times in minutes from 00:00
    joshua_busy = {
        "Monday": [(time_to_minutes("15:00"), time_to_minutes("15:30"))],
        "Tuesday": [
            (time_to_minutes("11:30"), time_to_minutes("12:00")),
            (time_to_minutes("13:00"), time_to_minutes("13:30")),
            (time_to_minutes("14:30"), time_to_minutes("15:00"))
        ],
        "Wednesday": []
    }
    
    # Joyce's busy times
    joyce_busy = {
        "Monday": [
            (time_to_minutes("9:00"), time_to_minutes("9:30")),
            (time_to_minutes("10:00"), time_to_minutes("11:00")),
            (time_to_minutes("11:30"), time_to_minutes("12:30")),
            (time_to_minutes("13:00"), time_to_minutes("15:00")),
            (time_to_minutes("15:30"), time_to_minutes("17:00"))
        ],
        "Tuesday": [
            (time_to_minutes("9:00"), time_to_minutes("17:00"))
        ],
        "Wednesday": [
            (time_to_minutes("9:00"), time_to_minutes("9:30")),
            (time_to_minutes("10:00"), time_to_minutes("11:00")),
            (time_to_minutes("12:30"), time_to_minutes("15:30")),
            (time_to_minutes("16:00"), time_to_minutes("16:30"))
        ]
    }
    
    days = ["Monday", "Tuesday", "Wednesday"]
    
    for day in days:
        for start in range(work_start, work_end - duration + 1, 30):
            end = start + duration
            if not is_free(joshua_busy, day, start, end):
                continue
            if not is_free(joyce_busy, day, start, end):
                continue
            # Joyce prefers not Monday before 12:00
            if day == "Monday" and end <= time_to_minutes("12:00"):
                continue
            # Found valid slot
            print(f"{day}:{minutes_to_time(start)}:{minutes_to_time(end)}")
            return
    
    print("No suitable slot found")

if __name__ == "__main__":
    main()