from z3 import *

def find_meeting_time():
    # Define the participants' blocked time slots in minutes from 9:00 (540 minutes from midnight)
    # Each blocked slot is a tuple (start, end) in minutes from 9:00 (0 is 9:00, 60 is 10:00, etc.)
    olivia_blocks = [(12*60 + 30 - 540, 13*60 + 30 - 540),  # 12:30-13:30
                     (14*60 + 30 - 540, 15*60 + 00 - 540),   # 14:30-15:00
                     (16*60 + 30 - 540, 17*60 + 00 - 540)]  # 16:30-17:00
    
    virginia_blocks = [(9*60 + 00 - 540, 10*60 + 00 - 540),  # 9:00-10:00
                       (11*60 + 30 - 540, 16*60 + 00 - 540),  # 11:30-16:00
                       (16*60 + 30 - 540, 17*60 + 00 - 540)]  # 16:30-17:00
    
    paul_blocks = [(9*60 + 00 - 540, 9*60 + 30 - 540),       # 9:00-9:30
                   (11*60 + 00 - 540, 11*60 + 30 - 540),     # 11:00-11:30
                   (13*60 + 00 - 540, 14*60 + 00 - 540),     # 13:00-14:00
                   (14*60 + 30 - 540, 16*60 + 00 - 540),     # 14:30-16:00
                   (16*60 + 30 - 540, 17*60 + 00 - 540)]      # 16:30-17:00
    
    # Anna has no meetings, so no blocks
    
    # Total working hours: 9:00-17:00 is 8 hours = 480 minutes
    # Meeting duration is 60 minutes
    meeting_duration = 60
    
    # Create a Z3 solver instance
    solver = Solver()
    
    # Define the start time variable (in minutes from 9:00)
    start_time = Int('start_time')
    
    # Constraints: start_time must be >= 0 (9:00) and <= 480 - 60 = 420 (since 420 +60 =480, which is 17:00)
    solver.add(start_time >= 0)
    solver.add(start_time <= 480 - meeting_duration)
    
    # Function to add constraints that the meeting does not overlap with any blocked slot
    def add_no_overlap_constraints(blocks):
        for (block_start, block_end) in blocks:
            # The meeting must be either entirely before the block or entirely after
            solver.add(Or(
                start_time + meeting_duration <= block_start,
                start_time >= block_end
            ))
    
    # Add constraints for each participant
    add_no_overlap_constraints(olivia_blocks)
    add_no_overlap_constraints(virginia_blocks)
    add_no_overlap_constraints(paul_blocks)
    
    # Check if there's a solution
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model.eval(start_time).as_long()
        
        # Convert start_minutes back to HH:MM format from 9:00 base
        total_minutes = 540 + start_minutes
        hours = total_minutes // 60
        minutes = total_minutes % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        
        end_minutes = total_minutes + meeting_duration
        end_hours = end_minutes // 60
        end_minutes = end_minutes % 60
        end_time_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

find_meeting_time()