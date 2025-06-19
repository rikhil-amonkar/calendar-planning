def main():
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    
    raymond_busy_all = {
        'Monday': [[0, 30], [150, 180], [240, 270], [360, 390]],
        'Tuesday': [],
        'Wednesday': [],
        'Thursday': [],
        'Friday': []
    }
    
    billy_busy_all = {
        'Monday': [[60, 90], [180, 240], [450, 480]],
        'Tuesday': [],
        'Wednesday': [],
        'Thursday': [],
        'Friday': []
    }
    
    donald_busy_all = {
        'Monday': [[0, 30], [60, 120], [180, 240], [300, 330], [420, 480]],
        'Tuesday': [],
        'Wednesday': [],
        'Thursday': [],
        'Friday': []
    }
    
    def is_free(busy_intervals, t):
        for s, e in busy_intervals:
            if t < e and t + 30 > s:
                return False
        return True

    candidate_slot = None
    candidate_day = None

    for day in days:
        for start_minutes in range(0, 451, 30):
            if (is_free(raymond_busy_all[day], start_minutes) and
                is_free(billy_busy_all[day], start_minutes) and
                is_free(donald_busy_all[day], start_minutes)):
                candidate_slot = [start_minutes, start_minutes + 30]
                candidate_day = day
                break
        if candidate_slot is not None:
            break

    if candidate_slot:
        def minutes_to_time(mins):
            hours = 9 + mins // 60
            minutes = mins % 60
            return f"{hours:02d}:{minutes:02d}"
        
        start_time = minutes_to_time(candidate_slot[0])
        end_time = minutes_to_time(candidate_slot[1])
        print(f"{start_time}-{end_time}")
        print(candidate_day)
    else:
        print("No meeting available")

if __name__ == "__main__":
    main()