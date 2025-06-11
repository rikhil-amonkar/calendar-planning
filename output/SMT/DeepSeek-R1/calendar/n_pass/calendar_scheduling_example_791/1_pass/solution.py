from z3 import *

def main():
    day = Int('day')
    start = Int('start')
    s = Solver()
    
    s.add(day >= 0, day <= 2)
    s.add(start >= 0)
    s.add(start + 30 <= 480)  # Meeting ends by 17:00 (480 minutes from 9:00)
    
    # Busy intervals for Nicole: half-open [start_minute, end_minute)
    nicole_intervals = {
        0: [(0, 30), (240, 270), (330, 390)],   # Monday
        1: [(0, 30), (150, 270), (330, 390)],    # Tuesday
        2: [(60, 120), (210, 360), (420, 480)]   # Wednesday
    }
    
    # Busy intervals for Ruth: half-open [start_minute, end_minute)
    ruth_intervals = {
        0: [(0, 480)],   # Monday (entire day)
        1: [(0, 480)],   # Tuesday (entire day)
        2: [(0, 90), (120, 150), (180, 210), (270, 390), (420, 450)]   # Wednesday
    }
    
    for d in [0, 1, 2]:
        nic_cons = []
        for (s_int, e_int) in nicole_intervals[d]:
            nic_cons.append(Or(start + 30 <= s_int, start >= e_int))
        
        ruth_cons = []
        for (s_int, e_int) in ruth_intervals[d]:
            ruth_cons.append(Or(start + 30 <= s_int, start >= e_int))
        
        if d == 2:  # Wednesday: meeting must end by 13:30 (270 minutes)
            ruth_cons.append(start + 30 <= 270)
        
        s.add(If(day == d, And(And(nic_cons), And(ruth_cons)), True)
    
    if s.check() == sat:
        m = s.model()
        d_val = m[day].as_long()
        start_val = m[start].as_long()
        
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[d_val]
        
        total_minutes = start_val
        hours = total_minutes // 60
        minutes = total_minutes % 60
        start_hour = 9 + hours
        start_min_str = f"{minutes:02d}"
        start_time_str = f"{start_hour}:{start_min_str}"
        
        end_minutes = start_val + 30
        hours_end = end_minutes // 60
        minutes_end = end_minutes % 60
        end_hour = 9 + hours_end
        end_min_str = f"{minutes_end:02d}"
        end_time_str = f"{end_hour}:{end_min_str}"
        
        print(f"Day: {day_str}")
        print(f"Start: {start_time_str}")
        print(f"End: {end_time_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()