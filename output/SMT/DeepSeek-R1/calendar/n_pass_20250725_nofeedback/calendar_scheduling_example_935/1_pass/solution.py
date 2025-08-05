from z3 import *

def main():
    days_list = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    
    terry_str = "Monday during 10:30 to 11:00, 12:30 to 14:00, 15:00 to 17:00, Tuesday during 9:30 to 10:00, 10:30 to 11:00, 14:00 to 14:30, 16:00 to 16:30, Wednesday during 9:30 to 10:30, 11:00 to 12:00, 13:00 to 13:30, 15:00 to 16:00, 16:30 to 17:00, Thursday during 9:30 to 10:00, 12:00 to 12:30, 13:00 to 14:30, 16:00 to 16:30, Friday during 9:00 to 11:30, 12:00 to 12:30, 13:30 to 16:00, 16:30 to 17:00"
    frances_str = "Monday during 9:30 to 11:00, 11:30 to 13:00, 14:00 to 14:30, 15:00 to 16:00, Tuesday during 9:00 to 9:30, 10:00 to 10:30, 11:00 to 12:00, 13:00 to 14:30, 15:30 to 16:30, Wednesday during 9:30 to 10:00, 10:30 to 11:00, 11:30 to 16:00, 16:30 to 17:00, Thursday during 11:00 to 12:30, 14:30 to 17:00, Friday during 9:30 to 10:30, 11:00 to 12:30, 13:00 to 16:00, 16:30 to 17:00"

    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        return hour * 60 + minute

    def parse_busy(s):
        busy_dict = {day: [] for day in days_list}
        tokens = s.split(',')
        current_day = None
        for token in tokens:
            token = token.strip()
            found_day = None
            for day in days_list:
                if token.startswith(day):
                    found_day = day
                    current_day = day
                    rest = token[len(day):].strip()
                    if rest.startswith('during'):
                        rest = rest[len('during'):].strip()
                    if rest:
                        parts = rest.split('to')
                        if len(parts) == 2:
                            start_str = parts[0].strip()
                            end_str = parts[1].strip()
                            start_min = time_to_minutes(start_str)
                            end_min = time_to_minutes(end_str)
                            busy_dict[current_day].append((start_min, end_min))
                    break
            if found_day is None and current_day is not None:
                parts = token.split('to')
                if len(parts) == 2:
                    start_str = parts[0].strip()
                    end_str = parts[1].strip()
                    start_min = time_to_minutes(start_str)
                    end_min = time_to_minutes(end_str)
                    busy_dict[current_day].append((start_min, end_min))
        return busy_dict

    terry_busy_dict = parse_busy(terry_str)
    frances_busy_dict = parse_busy(frances_str)
    
    terry_busy_by_index = [terry_busy_dict[day] for day in days_list]
    frances_busy_by_index = [frances_busy_dict[day] for day in days_list]

    d = Int('d')
    s = Int('s')
    opt = Optimize()
    
    opt.add(d >= 0, d <= 4)
    opt.add(s >= 540, s <= 990)
    
    for day_idx in range(5):
        for (start_b, end_b) in terry_busy_by_index[day_idx]:
            opt.add(Implies(d == day_idx, Or(s + 30 <= start_b, s >= end_b)))
        for (start_b, end_b) in frances_busy_by_index[day_idx]:
            opt.add(Implies(d == day_idx, Or(s + 30 <= start_b, s >= end_b)))
    
    total_minutes = d * 1440 + s
    opt.minimize(total_minutes)
    
    if opt.check() == sat:
        model = opt.model()
        day_idx = model[d].as_long()
        start_min = model[s].as_long()
        end_min = start_min + 30
        
        day_name = days_list[day_idx]
        start_hour = start_min // 60
        start_minute = start_min % 60
        end_hour = end_min // 60
        end_minute = end_min % 60
        
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()