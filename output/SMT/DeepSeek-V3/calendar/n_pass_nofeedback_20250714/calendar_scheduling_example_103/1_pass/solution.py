from z3 import *

def find_meeting_time():
    # Participants' blocked time slots on Monday (in 24-hour format)
    blocked_slots = {
        'Diane': [(9, 30, 10, 0), (14, 30, 15, 0)],
        'Jack': [(13, 30, 14, 0), (14, 30, 15, 0)],
        'Eugene': [(9, 0, 10, 0), (10, 30, 11, 30), (12, 0, 14, 30), (15, 0, 16, 30)],
        'Patricia': [(9, 30, 10, 30), (11, 0, 12, 0), (12, 30, 14, 0), (15, 0, 16, 30)]
    }
    
    # Create a Z3 solver instance
    solver = Solver()
    
    # Meeting duration is 30 minutes
    meeting_duration = 30
    
    # Possible meeting start times are from 9:00 to 16:30 (since meeting is 30 minutes)
    # Represent start time in minutes since 9:00 (0 to 450 minutes, since 9:00-17:00 is 8 hours = 480 minutes)
    start_time = Int('start_time')
    solver.add(start_time >= 0)  # 9:00 is 0 minutes
    solver.add(start_time <= 450)  # 16:30 is 450 minutes (16*60 +30 - 9*60 = 450)
    
    # Function to check if the meeting time overlaps with any blocked slot
    def is_overlap(meeting_start, meeting_end, block_start, block_end):
        # Convert block times to minutes since 9:00
        block_start_min = (block_start[0] - 9) * 60 + block_start[1]
        block_end_min = (block_end[0] - 9) * 60 + block_end[1]
        # Check if the meeting overlaps with the block
        return Or(
            And(meeting_start >= block_start_min, meeting_start < block_end_min),
            And(meeting_end > block_start_min, meeting_end <= block_end_min),
            And(meeting_start <= block_start_min, meeting_end >= block_end_min)
        )
    
    # For each participant, ensure the meeting does not overlap with any of their blocked slots
    for participant, slots in blocked_slots.items():
        constraints = []
        for slot in slots:
            block_start_hr, block_start_min, block_end_hr, block_end_min = slot
            meeting_end_time = start_time + meeting_duration
            overlap = is_overlap(start_time, meeting_end_time, 
                                (block_start_hr, block_start_min), 
                                (block_end_hr, block_end_min))
            constraints.append(Not(overlap))
        # The meeting should not overlap with any of the participant's blocked slots
        solver.add(And(constraints))
    
    # Check if a solution exists
    if solver.check() == sat:
        model = solver.model()
        start_min = model.eval(start_time).as_long()
        start_hr = 9 + start_min // 60
        start_min_remainder = start_min % 60
        end_min = start_min + meeting_duration
        end_hr = 9 + end_min // 60
        end_min_remainder = end_min % 60
        
        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hr:02d}:{start_min_remainder:02d}")
        print(f"End Time: {end_hr:02d}:{end_min_remainder:02d}")
    else:
        print("No solution found")

find_meeting_time()