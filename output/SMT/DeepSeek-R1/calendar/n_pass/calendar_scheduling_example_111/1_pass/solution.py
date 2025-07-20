from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Define start time variable in minutes from 9:00
    start = Int('start')
    meeting_duration = 30
    
    # Constraint: meeting within work hours (9:00 to 17:00)
    s.add(start >= 0)
    s.add(start + meeting_duration <= 480)  # 17:00 is 480 minutes from 9:00
    
    # Busy slots in minutes from 9:00
    gregory_busy = [(0, 60), (90, 150), (210, 240), (270, 300)]
    christine_busy = [(0, 150), (270, 480)]
    vincent_busy = [(0, 30), (90, 180), (210, 300), (330, 480)]
    # Natalie has no busy slots
    
    # Function to add constraints for a participant's busy slots
    def add_busy_constraints(busy_slots):
        constraints = []
        for (busy_start, busy_end) in busy_slots:
            # Meeting must be either before the busy slot or after it
            constraints.append(Or(start + meeting_duration <= busy_start, start >= busy_end))
        s.add(And(constraints))
    
    # Add constraints for each participant with busy slots
    add_busy_constraints(gregory_busy)
    add_busy_constraints(christine_busy)
    add_busy_constraints(vincent_busy)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        start_minutes = m[start].as_long()
        
        # Convert start_minutes back to time string
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = start_minutes + meeting_duration
        end_hours = 9 + end_minutes // 60
        end_minutes = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes:02d}"
        
        # Output solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()