from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    solver = Solver()
    
    # Work hours: 9:00 to 17:00 (9*60 to 17*60 in minutes)
    work_start = 9 * 60
    work_end = 17 * 60
    meeting_duration = 30
    
    # Define the start time of the meeting in minutes from 9:00
    start_time = Int('start_time')
    
    # Constraint: Meeting must start within work hours and end by work end time
    solver.add(start_time >= work_start)
    solver.add(start_time + meeting_duration <= work_end)
    
    # Participants' busy times in minutes from 9:00
    # Format: (start, end) in minutes
    jose_busy = [(11*60, 11*60 + 30), (12*60 + 30, 13*60)]
    keith_busy = [(14*60, 14*60 + 30), (15*60, 15*60 + 30)]
    logan_busy = [(9*60, 10*60), (12*60, 12*60 + 30), (15*60, 15*60 + 30)]
    megan_busy = [(9*60, 10*60 + 30), (11*60, 12*60), (13*60, 13*60 + 30), (14*60 + 30, 16*60 + 30)]
    gary_busy = [(9*60, 9*60 + 30), (10*60, 10*60 + 30), (11*60 + 30, 13*60), (13*60 + 30, 14*60), (14*60 + 30, 16*60 + 30)]
    bobby_busy = [(11*60, 11*60 + 30), (12*60, 12*60 + 30), (13*60, 16*60)]
    
    # Function to add constraints that the meeting does not overlap with busy times
    def add_no_overlap(busy_slots):
        for (busy_start, busy_end) in busy_slots:
            solver.add(Or(
                start_time + meeting_duration <= busy_start,
                start_time >= busy_end
            ))
    
    # Add no-overlap constraints for each participant
    add_no_overlap(jose_busy)
    add_no_overlap(keith_busy)
    add_no_overlap(logan_busy)
    add_no_overlap(megan_busy)
    add_no_overlap(gary_busy)
    add_no_overlap(bobby_busy)
    
    # Additional constraint: Jose does not want to meet after 15:30
    solver.add(start_time + meeting_duration <= 15*60 + 30)
    
    # Check if a solution exists
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model.evaluate(start_time).as_long()
        
        # Convert minutes back to HH:MM format
        hours = start_minutes // 60
        minutes = start_minutes % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        
        end_minutes = start_minutes + meeting_duration
        end_hours = end_minutes // 60
        end_minutes = end_minutes % 60
        end_time_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        # Print the solution in the required format
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()