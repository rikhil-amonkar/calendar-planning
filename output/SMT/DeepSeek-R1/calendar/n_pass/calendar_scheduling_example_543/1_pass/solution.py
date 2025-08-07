from z3 import Solver, Int, Or, sat

def main():
    s = Solver()
    start = Int('start')
    
    # Meeting must be within 9:00 to 17:00 and last 60 minutes
    s.add(start >= 0)
    s.add(start <= 420)  # 16:00 in minutes (since 17:00 - 60 minutes = 16:00)
    
    # James' busy intervals in minutes (from 9:00)
    james_busy = [(150, 180), (330, 360)]
    for b_start, b_end in james_busy:
        s.add(Or(start + 60 <= b_start, start >= b_end))
    
    # John's busy intervals in minutes (from 9:00)
    john_busy = [(30, 120), (150, 180), (210, 270), (330, 450)]
    for b_start, b_end in john_busy:
        s.add(Or(start + 60 <= b_start, start >= b_end))
    
    if s.check() == sat:
        m = s.model()
        start_min = m[start].as_long()
        
        # Convert start_min to HH:MM
        total_min = start_min
        hours = 9 + total_min // 60
        minutes = total_min % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time (start_min + 60 minutes)
        end_min = start_min + 60
        hours_end = 9 + end_min // 60
        minutes_end = end_min % 60
        end_time = f"{hours_end:02d}:{minutes_end:02d}"
        
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()