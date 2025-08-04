from z3 import *

def solve_scheduling():
    # Initialize the solver
    solver = Solver()
    
    # Define the work hours (9:00 to 17:00)
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    
    # Meeting duration is 1 hour (60 minutes)
    meeting_duration = 60
    
    # Define the start time of the meeting as an integer variable (in minutes)
    start_time = Int('start_time')
    
    # Constraint: start_time must be within work hours and leave enough time for the meeting
    solver.add(start_time >= work_start)
    solver.add(start_time + meeting_duration <= work_end)
    
    # Define each participant's blocked time intervals in minutes since midnight
    # Olivia's blocked times: 12:30-13:30, 14:30-15:00, 16:30-17:00
    olivia_blocked = [(12*60 + 30, 13*60 + 30), (14*60 + 30, 15*60), (16*60 + 30, 17*60)]
    
    # Anna has no meetings
    anna_blocked = []
    
    # Virginia's blocked times: 9:00-10:00, 11:30-16:00, 16:30-17:00
    virginia_blocked = [(9*60, 10*60), (11*60 + 30, 16*60), (16*60 + 30, 17*60)]
    
    # Paul's blocked times: 9:00-9:30, 11:00-11:30, 13:00-14:00, 14:30-16:00, 16:30-17:00
    paul_blocked = [(9*60, 9*60 + 30), (11*60, 11*60 + 30), (13*60, 14*60), (14*60 + 30, 16*60), (16*60 + 30, 17*60)]
    
    # Function to check if the meeting time overlaps with any blocked intervals
    def no_overlap(start, duration, blocked_intervals):
        for (block_start, block_end) in blocked_intervals:
            # The meeting should not overlap with any blocked interval
            solver.add(Not(And(start < block_end, start + duration > block_start)))
    
    # Add constraints for each participant
    no_overlap(start_time, meeting_duration, olivia_blocked)
    no_overlap(start_time, meeting_duration, anna_blocked)  # Anna has no blocked times, so no constraints
    no_overlap(start_time, meeting_duration, virginia_blocked)
    no_overlap(start_time, meeting_duration, paul_blocked)
    
    # Check if there's a solution
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model.evaluate(start_time).as_long()
        
        # Convert minutes back to HH:MM format
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        end_minutes = start_minutes + meeting_duration
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hour:02d}:{start_minute:02d}")
        print(f"End Time: {end_hour:02d}:{end_minute:02d}")
    else:
        print("No solution found")

solve_scheduling()