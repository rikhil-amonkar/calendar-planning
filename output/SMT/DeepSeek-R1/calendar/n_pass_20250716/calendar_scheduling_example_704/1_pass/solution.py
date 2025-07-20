from z3 import *

def main():
    # Define the variables
    day = Int('day')
    s = Int('s')  # start time in minutes after 9:00 on the chosen day

    # Precomputed free intervals for Samuel for Monday, Tuesday, Wednesday
    # Each interval is (start_minutes, end_minutes) relative to 9:00
    free_intervals = [
        [ (0, 90), (120, 180), (210, 240), (360, 390), (450, 480) ],   # Monday
        [ (180, 300), (390, 450) ],                                     # Tuesday
        [ (0, 90), (120, 150), (180, 210), (240, 300), (330, 360), (420, 480) ]  # Wednesday
    ]

    # Condition: the meeting must fit into one of the free intervals of the chosen day
    cond = False
    for d, day_intervals in enumerate(free_intervals):
        for interval in day_intervals:
            a, b = interval
            # The meeting [s, s+30) must be within [a, b)
            # So: s >= a and s+30 <= b  => s <= b-30
            cond = Or(cond, And(day == d, s >= a, s <= b-30))
    
    solver = Optimize()
    solver.add(day >= 0, day <= 2)
    solver.add(s >= 0, s <= 450)  # 450 = 480 (8 hours) - 30 minutes
    solver.add(cond)
    
    # Total minutes from Monday 00:00 to the meeting start time
    # Monday 9:00 is 9*60 = 540 minutes from Monday 00:00
    total_minutes = day * 1440 + 540 + s
    solver.minimize(total_minutes)
    
    if solver.check() == sat:
        m = solver.model()
        d_val = m[day].as_long()
        s_val = m[s].as_long()
        
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[d_val]
        
        total_minutes_start = 9 * 60 + s_val
        hours = total_minutes_start // 60
        minutes = total_minutes_start % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        total_minutes_end = total_minutes_start + 30
        end_hours = total_minutes_end // 60
        end_minutes = total_minutes_end % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        
        print(day_str)
        print(start_time)
        print(end_time)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()