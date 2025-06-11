from z3 import Solver, Int, Or, And, sat

def main():
    # Initialize solver
    s = Solver()
    
    # Define the start time variable S (in minutes from 9:00)
    start_time = Int('start_time')
    
    # Constraints: 360 <= start_time <= 450 (since meeting is 30 minutes, must end by 480)
    s.add(start_time >= 360)
    s.add(start_time <= 450)
    
    # Busy intervals for each participant (in minutes from 9:00)
    # Katherine: [180, 210], [240, 330]
    # Julie: [0, 30], [90, 120], [270, 300], [360, 390]
    # Angela: [0, 60], [90, 120], [150, 300], [330, 360], [450, 480]
    # Nicholas: [30, 120], [150, 270], [300, 420], [450, 480]
    # Carl: [0, 120], [150, 210], [240, 330], [360, 420], [450, 480]
    
    # Katherine's constraints
    s.add(Or(start_time + 30 <= 180, start_time >= 210))
    s.add(Or(start_time + 30 <= 240, start_time >= 330))
    
    # Julie's constraints
    s.add(Or(start_time + 30 <= 0, start_time >= 30))
    s.add(Or(start_time + 30 <= 90, start_time >= 120))
    s.add(Or(start_time + 30 <= 270, start_time >= 300))
    s.add(Or(start_time + 30 <= 360, start_time >= 390))
    
    # Angela's constraints
    s.add(Or(start_time + 30 <= 0, start_time >= 60))
    s.add(Or(start_time + 30 <= 90, start_time >= 120))
    s.add(Or(start_time + 30 <= 150, start_time >= 300))
    s.add(Or(start_time + 30 <= 330, start_time >= 360))
    s.add(Or(start_time + 30 <= 450, start_time >= 480))
    
    # Nicholas's constraints
    s.add(Or(start_time + 30 <= 30, start_time >= 120))
    s.add(Or(start_time + 30 <= 150, start_time >= 270))
    s.add(Or(start_time + 30 <= 300, start_time >= 420))
    s.add(Or(start_time + 30 <= 450, start_time >= 480))
    
    # Carl's constraints
    s.add(Or(start_time + 30 <= 0, start_time >= 120))
    s.add(Or(start_time + 30 <= 150, start_time >= 210))
    s.add(Or(start_time + 30 <= 240, start_time >= 330))
    s.add(Or(start_time + 30 <= 360, start_time >= 420))
    s.add(Or(start_time + 30 <= 450, start_time >= 480))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        start_minutes = model[start_time].as_long()
        # Convert minutes back to time
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        end_minutes = start_minutes + 30
        end_hours = 9 + end_minutes // 60
        end_minutes = end_minutes % 60
        end_time_str = f"{end_hours:02d}:{end_minutes:02d}"
        print(f"Meeting can be scheduled from {start_time_str} to {end_time_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()