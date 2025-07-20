from z3 import Solver, Int, Or, sat

def main():
    # Initialize solver
    s = Solver()
    
    # Start time in minutes from 9:00 (0 to 450 inclusive, since 450+30=480 is 17:00)
    start = Int('start')
    s.add(start >= 0)
    s.add(start <= 450)
    
    # Busy intervals for each participant (in minutes from 9:00)
    busy_intervals = {
        'Cynthia': [(0, 30), (60, 90), (270, 330), (360, 420)],
        'Ann': [(60, 120), (240, 270), (300, 360), (420, 450)],
        'Catherine': [(0, 150), (210, 270), (330, 480)],
        'Kyle': [(0, 30), (60, 150), (180, 210), (240, 330), (360, 420)]
    }
    
    # Add constraints: for each participant and each busy interval, ensure no overlap
    for person, intervals in busy_intervals.items():
        for (b_start, b_end) in intervals:
            s.add(Or(start + 30 <= b_start, start >= b_end))
    
    # Check for solution
    if s.check() == sat:
        m = s.model()
        start_val = m[start].as_long()
        
        # Calculate start time in HH:MM
        total_minutes_start = start_val
        hours_start = 9 + total_minutes_start // 60
        minutes_start = total_minutes_start % 60
        start_time_str = f"{hours_start:02d}:{minutes_start:02d}"
        
        # Calculate end time in HH:MM (start time + 30 minutes)
        total_minutes_end = start_val + 30
        hours_end = 9 + total_minutes_end // 60
        minutes_end = total_minutes_end % 60
        end_time_str = f"{hours_end:02d}:{minutes_end:02d}"
        
        # Output the solution in the required format
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()