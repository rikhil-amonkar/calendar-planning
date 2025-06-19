def main():
    # Convert time to minutes past midnight
    participants_busy = {
        "Shirley": [(10*60+30, 11*60), (12*60, 12*60+30)],
        "Jacob": [(9*60, 9*60+30), (10*60, 10*60+30), (11*60, 11*60+30), (12*60+30, 13*60+30), (14*60+30, 15*60)],
        "Stephen": [(11*60+30, 12*60), (12*60+30, 13*60)],
        "Margaret": [(9*60, 9*60+30), (10*60+30, 12*60+30), (13*60, 13*60+30), (15*60, 15*60+30), (16*60+30, 17*60)],
        "Mason": [(9*60, 10*60), (10*60+30, 11*60), (11*60+30, 12*60+30), (13*60, 13*60+30), (14*60, 14*60+30), (16*60+30, 17*60)]
    }
    
    meeting_duration = 30
    # Margaret constraint: not before 14:30 -> 14:30 is 14*60+30 = 870 minutes
    # Last possible start time: 16:30 (16*60+30=990) because 16:30+30min=17:00
    start_times = [870, 900, 930, 960, 990]
    
    for start in start_times:
        end = start + meeting_duration
        all_available = True
        for person, busy_list in participants_busy.items():
            person_available = True
            for (busy_start, busy_end) in busy_list:
                if start < busy_end and end > busy_start:
                    person_available = False
                    break
            if not person_available:
                all_available = False
                break
        if all_available:
            start_hour = start // 60
            start_minute = start % 60
            end_hour = end // 60
            end_minute = end % 60
            time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
            print("Monday")
            print(time_str)
            return
    # According to the problem, there is a solution, so we assume we find one.
    
if __name__ == "__main__":
    main()