from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Define the start time variable (in minutes)
    S = Int('S')
    
    # Meeting duration is 30 minutes
    meeting_duration = 30
    
    # Work hours: 9:00 (540) to 17:00 (1020)
    work_start = 540
    work_end = 1020
    
    # Constraint: meeting must start between 9:00 and 16:30 (so that it ends by 17:00)
    s.add(S >= work_start, S <= work_end - meeting_duration)
    
    # Busy intervals for each person in minutes
    # Jacob
    jacob_busy = [(13*60+30, 14*60), (14*60+30, 15*60)]
    # Diana
    diana_busy = [(9*60+30, 10*60), (11*60+30, 12*60), (13*60, 13*60+30), (16*60, 16*60+30)]
    # Adam
    adam_busy = [(9*60+30, 10*60+30), (11*60, 12*60+30), (15*60+30, 16*60)]
    # Angela
    angela_busy = [(9*60+30, 10*60), (10*60+30, 12*60), (13*60, 15*60+30), (16*60, 16*60+30)]
    # Dennis
    dennis_busy = [(9*60, 9*60+30), (10*60+30, 11*60+30), (13*60, 15*60), (16*60+30, 17*60)]
    
    # Combine all busy intervals
    all_busy = jacob_busy + diana_busy + adam_busy + angela_busy + dennis_busy
    
    # For each busy interval, add constraint that meeting does not overlap
    for (busy_start, busy_end) in all_busy:
        s.add(Or(S + meeting_duration <= busy_start, S >= busy_end))
    
    # Check if there's a solution
    if s.check() == sat:
        model = s.model()
        start_minutes = model.eval(S).as_long()
        
        # Convert start_minutes to HH:MM
        start_hour = start_minutes // 60
        start_minute = start_minutes % 60
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        
        # Calculate end time
        end_minutes = start_minutes + meeting_duration
        end_hour = end_minutes // 60
        end_minute = end_minutes % 60
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print("Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()