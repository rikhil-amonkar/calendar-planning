from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Start time in minutes from 9:00 (0 minutes = 9:00)
    S = Int('S')
    
    # Total working minutes (9:00 to 17:00 is 8 hours = 480 minutes)
    total_minutes = 480
    meeting_duration = 30
    
    # Constraint: Meeting must be within working hours
    s.add(S >= 0)
    s.add(S + meeting_duration <= total_minutes)
    
    # Busy intervals for each participant (each interval is (start_minute, end_minute))
    bradley_busy = [(30, 60), (210, 240), (270, 300), (390, 420)]
    teresa_busy = [(90, 120), (180, 210), (240, 270), (330, 360)]
    elizabeth_busy = [(0, 30), (90, 150), (240, 270), (330, 360), (390, 480)]
    christian_busy = [(0, 30), (90, 480)]
    
    # Function to add constraints for a set of busy intervals
    def add_busy_constraints(busy_intervals):
        for start, end in busy_intervals:
            # The meeting should not overlap: either ends before the busy interval starts or starts after it ends
            s.add(Or(S + meeting_duration <= start, S >= end))
    
    # Add constraints for each participant
    add_busy_constraints(bradley_busy)
    add_busy_constraints(teresa_busy)
    add_busy_constraints(elizabeth_busy)
    add_busy_constraints(christian_busy)
    
    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        start_minutes = model[S].as_long()
        
        # Convert start_minutes back to time string
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = start_minutes + meeting_duration
        end_hours = 9 + end_minutes // 60
        end_minutes = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()