from z3 import *

def schedule_meeting(kayla_schedule, rebecca_schedule, meeting_duration):
    # Define the day of the week (Monday)
    day = 0
    
    # Define the start and end time of the work hours
    start_time = 9
    end_time = 17
    
    # Define the meeting duration
    meeting_start = 0
    meeting_end = meeting_duration
    
    # Create a Z3 solver
    s = Solver()
    
    # Define the variables for the start time of the meeting
    start_time_var = Int('start_time')
    
    # Add constraints for the start time to be within work hours
    s.add(And(start_time <= start_time_var, start_time_var <= end_time - meeting_duration))
    
    # Add constraints for Kayla's schedule
    for block_start, block_end in kayla_schedule:
        s.add(Or(start_time_var >= block_end, (start_time_var + meeting_duration) <= block_start))
    
    # Add constraints for Rebecca's schedule
    for block_start, block_end in rebecca_schedule:
        s.add(Or(start_time_var >= block_end, (start_time_var + meeting_duration) <= block_start))
    
    # Check if there is a solution
    if s.check() == sat:
        # Get the solution
        model = s.model()
        start_time = model[start_time_var].as_long()
        
        # Print the solution
        print(f"SOLUTION:")
        print(f"Day: {day}")
        print(f"Start Time: {start_time:02d}:00")
        print(f"End Time: {(start_time + meeting_duration):02d}:00")
    else:
        print("No solution found")

# Example usage
kayla_schedule = [(10*60, 10*60+30), (14*60+30, 16*60)]
rebecca_schedule = [(9*60, 13*60), (13*60+30, 15*60), (15*60+30, 16*60)]
meeting_duration = 60

schedule_meeting(kayla_schedule, rebecca_schedule, meeting_duration)