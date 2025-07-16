from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()
    
    # Work hours: 9:00 to 17:00 (540 to 1020 minutes)
    work_start = 540  # 9:00 in minutes
    work_end = 1020    # 17:00 in minutes
    meeting_duration = 30
    
    # Define the start time variable (in minutes since 9:00, so 0 is 9:00)
    start = Int('start')
    s.add(start >= 0)
    s.add(start + meeting_duration <= work_end - work_start)
    
    # Each participant's blocked times in minutes since 9:00
    # Doris's blocked times: 9:00-11:00 (0-120), 13:30-14:00 (270-300), 16:00-16:30 (420-450)
    doris_blocks = [(0, 120), (270, 300), (420, 450)]
    # Theresa's blocked times: 10:00-12:00 (60-180)
    theresa_blocks = [(60, 180)]
    # Christian has no blocks
    christian_blocks = []
    # Terry's blocked times: 9:30-10:00 (30-60), 11:30-12:00 (150-180), 12:30-13:00 (210-240), 13:30-14:00 (270-300), 14:30-15:00 (330-360), 15:30-17:00 (390-480)
    terry_blocks = [(30, 60), (150, 180), (210, 240), (270, 300), (330, 360), (390, 480)]
    # Carolyn's blocked times: 9:00-10:30 (0-90), 11:00-11:30 (120-150), 12:00-13:00 (180-240), 13:30-14:30 (270-330), 15:00-17:00 (360-480)
    carolyn_blocks = [(0, 90), (120, 150), (180, 240), (270, 330), (360, 480)]
    # Kyle's blocked times: 9:00-9:30 (0-30), 11:30-12:00 (150-180), 12:30-13:00 (210-240), 14:30-17:00 (330-480)
    kyle_blocks = [(0, 30), (150, 180), (210, 240), (330, 480)]
    
    # Function to add constraints for each participant's blocks
    def add_participant_constraints(blocks):
        for block in blocks:
            block_start, block_end = block
            # The meeting must not overlap with the block: meeting is before or after
            s.add(Or(start + meeting_duration <= block_start, start >= block_end))
    
    # Add constraints for each participant
    add_participant_constraints(doris_blocks)
    add_participant_constraints(theresa_blocks)
    add_participant_constraints(christian_blocks)
    add_participant_constraints(terry_blocks)
    add_participant_constraints(carolyn_blocks)
    add_participant_constraints(kyle_blocks)
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        start_minutes = model[start].as_long()
        # Convert start minutes back to time
        total_minutes = work_start + start_minutes
        hours = total_minutes // 60
        minutes = total_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        end_minutes = total_minutes + meeting_duration
        end_hours = end_minutes // 60
        end_minutes_remainder = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes_remainder:02d}"
        
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

solve_scheduling()