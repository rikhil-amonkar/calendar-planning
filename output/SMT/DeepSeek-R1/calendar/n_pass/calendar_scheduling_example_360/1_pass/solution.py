from z3 import *

def main():
    s = Solver()
    S = Int('S')
    
    # Constraints: S must be between 0 and 450 minutes (9:00 to 16:30 start)
    s.add(S >= 0)
    s.add(S <= 450)
    
    # Busy intervals for each person (each interval is (start_minutes, end_minutes))
    emily = [(60, 90), (420, 450)]
    mason = []
    maria = [(90, 120), (300, 330)]
    carl = [(30, 60), (90, 210), (270, 300), (330, 390), (420, 480)]
    david = [(30, 120), (150, 180), (210, 270), (300, 360), (420, 480)]
    frank = [(30, 90), (120, 150), (210, 270), (330, 480)]
    
    persons = [emily, mason, maria, carl, david, frank]
    
    # Add constraints for each busy interval
    for person in persons:
        for (start, end) in person:
            s.add(Or(S + 30 <= start, S >= end))
    
    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        start_minutes = model[S].as_long()
        
        # Convert start_minutes to time string (HH:MM)
        total_minutes = start_minutes
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time (start_minutes + 30 minutes)
        total_minutes_end = start_minutes + 30
        hours_end = 9 + total_minutes_end // 60
        minutes_end = total_minutes_end % 60
        end_time = f"{hours_end:02d}:{minutes_end:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found, but the problem states there is one.")

if __name__ == "__main__":
    main()