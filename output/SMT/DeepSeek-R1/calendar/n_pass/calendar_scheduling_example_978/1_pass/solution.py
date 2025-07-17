from z3 import *

def time_str_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return hours * 60 + minutes

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def parse_schedule(s, name):
    prefix = name + " is busy on "
    if not s.startswith(prefix):
        return None
    s_clean = s[len(prefix):]
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    result = {day: [] for day in days}
    tokens = s_clean.split()
    current_day = None
    i = 0
    n = len(tokens)
    while i < n:
        token = tokens[i].rstrip(',')
        if token in days:
            current_day = token
            i += 1
            if i < n and tokens[i] == 'during':
                i += 1
        else:
            if i+2 >= n:
                break
            if tokens[i+1] != 'to':
                i += 1
                continue
            start_str = token
            end_str = tokens[i+2].rstrip(',')
            if current_day is not None:
                result[current_day].append((start_str, end_str))
            i += 3
    return result

def main():
    brian_str = "Brian is busy on Monday during 9:30 to 10:00, 12:30 to 14:30, 15:30 to 16:00, Tuesday during 9:00 to 9:30, Wednesday during 12:30 to 14:00, 16:30 to 17:00, Thursday during 11:00 to 11:30, 13:00 to 13:30, 16:30 to 17:00, Friday during 9:30 to 10:00, 10:30 to 11:00, 13:00 to 13:30, 15:00 to 16:00, 16:30 to 17:00"
    julia_str = "Julia is busy on Monday during 9:00 to 10:00, 11:00 to 11:30, 12:30 to 13:00, 15:30 to 16:00, Tuesday during 13:00 to 14:00, 16:00 to 16:30, Wednesday during 9:00 to 11:30, 12:00 to 12:30, 13:00 to 17:00, Thursday during 9:00 to 10:30, 11:00 to 17:00, Friday during 9:00 to 10:00, 10:30 to 11:30, 12:30 to 14:00, 14:30 to 15:00, 15:30 to 16:00"
    
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    brian_busy = parse_schedule(brian_str, "Brian")
    julia_busy = parse_schedule(julia_str, "Julia")
    
    brian_busy_minutes = {day: [] for day in days}
    julia_busy_minutes = {day: [] for day in days}
    
    for day in days:
        for (s, e) in brian_busy[day]:
            s_min = time_str_to_minutes(s)
            e_min = time_str_to_minutes(e)
            brian_busy_minutes[day].append((s_min, e_min))
        for (s, e) in julia_busy[day]:
            s_min = time_str_to_minutes(s)
            e_min = time_str_to_minutes(e)
            julia_busy_minutes[day].append((s_min, e_min))
    
    D = Int('D')
    S = Int('S')
    base_constraints = [D >= 0, D <= 4, S >= 540, S <= 960]
    
    for day in days:
        d_index = days.index(day)
        for (s_busy, e_busy) in brian_busy_minutes[day]:
            base_constraints.append(Or(D != d_index, Or(S + 60 <= s_busy, S >= e_busy))
        for (s_busy, e_busy) in julia_busy_minutes[day]:
            base_constraints.append(Or(D != d_index, Or(S + 60 <= s_busy, S >= e_busy))
    
    o1 = Optimize()
    for c in base_constraints:
        o1.add(c)
    o1.add(D >= 1)
    total_time = D * 24 * 60 + S
    o1.minimize(total_time)
    
    if o1.check() == sat:
        m = o1.model()
    else:
        o2 = Optimize()
        for c in base_constraints:
            o2.add(c)
        total_time = D * 24 * 60 + S
        o2.minimize(total_time)
        o2.check()
        m = o2.model()
    
    day_index = m.eval(D).as_long()
    start_min = m.eval(S).as_long()
    end_min = start_min + 60
    day_str = days[day_index]
    start_time = minutes_to_time_str(start_min)
    end_time = minutes_to_time_str(end_min)
    
    print("SOLUTION:")
    print(f"Day: {day_str}")
    print(f"Start Time: {start_time}")
    print(f"End Time: {end_time}")

if __name__ == "__main__":
    main()