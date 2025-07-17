from z3 import *

def main():
    # Convert blocked times to minutes from 9:00
    participants_blocks = {
        'Joe': [(30, 60), (90, 120)],
        'Keith': [(150, 180), (360, 390)],
        'Patricia': [(0, 30), (240, 270)],
        'Nancy': [(0, 120), (150, 450)],
        'Pamela': [(0, 60), (90, 120), (150, 210), (240, 300), (330, 360), (390, 420), (450, 480)]
    }
    
    s = Int('s')
    solver = Solver()
    solver.add(s >= 0, s <= 15)
    s_slot = s * 30
    
    for blocks in participants_blocks.values():
        for (a, b) in blocks:
            solver.add(Or(s_slot + 30 <= a, s_slot >= b))
    
    if solver.check() == sat:
        m = solver.model()
        s_val = m.eval(s).as_long()
        start_minutes = s_val * 30
        hours = start_minutes // 60
        minutes = start_minutes % 60
        total_minutes_start = 9 * 60 + start_minutes
        start_hour = total_minutes_start // 60
        start_minute = total_minutes_start % 60
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        
        end_minutes = start_minutes + 30
        total_minutes_end = 9 * 60 + end_minutes
        end_hour = total_minutes_end // 60
        end_minute = total_minutes_end % 60
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()