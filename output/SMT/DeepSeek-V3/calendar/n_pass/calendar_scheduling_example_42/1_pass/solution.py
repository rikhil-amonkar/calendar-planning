from z3 import *

def find_meeting_time():
    # Define the work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 60  # 1 hour in minutes

    # Participants' busy slots in minutes since midnight
    julie_busy = [(9*60, 9*60 + 30), (11*60, 11*60 + 30), (12*60, 12*60 + 30), 
                  (13*60 + 30, 14*60), (16*60, 17*60)]
    sean_busy = [(9*60, 9*60 + 30), (13*60, 13*60 + 30), (15*60, 15*60 + 30), 
                 (16*60, 16*60 + 30)]
    lori_busy = [(10*60, 10*60 + 30), (11*60, 13*60), (15*60 + 30, 17*60)]

    # Create a Z3 solver instance
    solver = Solver()

    # Define the meeting start time as a Z3 variable
    meeting_start = Int('meeting_start')
    
    # Constraint: meeting must start within work hours and end before work ends
    solver.add(meeting_start >= work_start)
    solver.add(meeting_start + meeting_duration <= work_end)

    # Function to add constraints that the meeting does not overlap with busy slots
    def add_no_overlap_constraints(busy_slots):
        for start, end in busy_slots:
            solver.add(Or(meeting_start + meeting_duration <= start, meeting_start >= end))

    # Add no-overlap constraints for each participant
    add_no_overlap_constraints(julie_busy)
    add_no_overlap_constraints(sean_busy)
    add_no_overlap_constraints(lori_busy)

    # Check if a solution exists
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model[meeting_start].as_long()
        
        # Convert minutes back to HH:MM format
        start_hh = start_minutes // 60
        start_mm = start_minutes % 60
        end_minutes = start_minutes + meeting_duration
        end_hh = end_minutes // 60
        end_mm = end_minutes % 60
        
        # Format the output
        solution = (
            f"SOLUTION:\n"
            f"Day: Monday\n"
            f"Start Time: {start_hh:02d}:{start_mm:02d}\n"
            f"End Time: {end_hh:02d}:{end_mm:02d}"
        )
        return solution
    else:
        return "No solution found."

# Print the solution
print(find_meeting_time())