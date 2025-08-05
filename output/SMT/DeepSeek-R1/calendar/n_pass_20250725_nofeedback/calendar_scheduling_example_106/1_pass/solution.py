from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Start time in minutes from 9:00 (0 minutes = 9:00, 60 minutes = 10:00, etc.)
    start = Int('start')
    
    # Meeting duration is 60 minutes
    duration = 60
    
    # Total available time: 9:00 to 17:00 is 8 hours = 480 minutes
    # Meeting must end by 17:00, so start <= 480 - duration = 420
    s.add(start >= 0)
    s.add(start <= 420)
    
    # Blocked intervals for each participant (in minutes from 9:00)
    olivia_blocks = [(210, 270), (330, 360), (450, 480)]
    virginia_blocks = [(0, 60), (150, 420), (450, 480)]
    paul_blocks = [(0, 30), (120, 150), (240, 300), (330, 420), (450, 480)]
    
    # Anna has no blocks, so no constraints for her
    
    # Function to add constraints for each blocked interval
    def add_block_constraints(blocks):
        for b_start, b_end in blocks:
            # The meeting must either end before the block starts or start after the block ends
            s.add(Or(start + duration <= b_start, start >= b_end))
    
    # Add constraints for each participant
    add_block_constraints(olivia_blocks)
    add_block_constraints(virginia_blocks)
    add_block_constraints(paul_blocks)
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        start_minutes = model[start].as_long()
        
        # Convert start_minutes to time string (HH:MM)
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = start_minutes + duration
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