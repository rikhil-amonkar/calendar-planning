from z3 import *

def main():
    # Initialize the optimizer
    opt = Optimize()
    
    # Start time in minutes from 9:00
    start = Int('start')
    opt.add(start >= 0)
    opt.add(start <= 450)  # 450 minutes = 16:30, ensuring meeting ends by 17:00
    
    # Busy intervals for each participant (start, end) in minutes from 9:00
    busy_times = {
        'Cynthia': [(30, 90), (150, 180), (240, 270), (360, 420)],
        'Lauren': [(0, 30), (90, 120), (150, 180), (240, 270), (300, 330), (360, 390), (420, 480)],
        'Robert': [(90, 120), (150, 180), (210, 270), (300, 420)]
    }
    
    # Add constraints for each participant's busy intervals
    for intervals in busy_times.values():
        for (busy_start, busy_end) in intervals:
            opt.add(Or(start + 30 <= busy_start, start >= busy_end))
    
    # Minimize the start time to find the earliest slot
    opt.minimize(start)
    
    # Check for a solution
    if opt.check() == sat:
        m = opt.model()
        start_val = m[start].as_long()
        
        # Convert start_val to HH:MM format
        total_minutes = start_val
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time (start + 30 minutes)
        end_val = start_val + 30
        end_hours = 9 + end_val // 60
        end_minutes = end_val % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()