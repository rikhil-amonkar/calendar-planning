def main():
    participants = ['Katherine', 'Rebecca', 'Julie', 'Angela', 'Nicholas', 'Carl']
    
    busy_times = {
        'Katherine': [(12*60, 12*60+30), (13*60, 14*60+30)],
        'Rebecca': [],
        'Julie': [(9*60, 9*60+30), (10*60+30, 11*60), (13*60+30, 14*60), (15*60, 15*60+30)],
        'Angela': [(9*60, 10*60), (10*60+30, 11*60), (11*60+30, 14*60), (14*60+30, 15*60), (16*60+30, 17*60)],
        'Nicholas': [(9*60+30, 11*60), (11*60+30, 13*60+30), (14*60, 16*60), (16*60+30, 17*60)],
        'Carl': [(9*60, 11*60), (11*60+30, 12*60+30), (13*60, 14*60+30), (15*60, 16*60), (16*60+30, 17*60)]
    }
    
    day = "Monday"
    start_min = 15 * 60
    start_max = 16 * 60
    
    for start in range(start_min, start_max + 1):
        end = start + 30
        valid = True
        for participant in participants:
            busy_list = busy_times[participant]
            for (busy_start, busy_end) in busy_list:
                if start < busy_end and end > busy_start:
                    valid = False
                    break
            if not valid:
                break
        if valid:
            start_h = start // 60
            start_m = start % 60
            end_h = end // 60
            end_m = end % 60
            time_str = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
            print(day)
            print(time_str)
            return
    
    print("No valid slot found")

if __name__ == "__main__":
    main()