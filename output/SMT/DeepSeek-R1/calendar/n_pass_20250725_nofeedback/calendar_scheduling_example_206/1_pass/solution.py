from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Convert time to minutes
    work_start = 9 * 60  # 09:00 -> 540 minutes
    work_end = 17 * 60   # 17:00 -> 1020 minutes
    meeting_duration = 30
    
    # Margaret's constraint: meeting must start at or after 14:30 (870 minutes)
    margaret_min_time = 14 * 60 + 30  # 14:30 -> 870 minutes
    # The latest start time is work_end - meeting_duration = 1020 - 30 = 990 minutes (16:30)
    
    # Define the start time variable (in minutes)
    start = Int('start')
    
    # Constrain start time to be within valid working hours and after Margaret's constraint
    s.add(start >= margaret_min_time)  # at or after 14:30
    s.add(start <= work_end - meeting_duration)  # no later than 16:30
    
    # Busy time intervals for each participant (in minutes)
    # Format: list of (start_minute, end_minute) for each busy slot
    shirley_busy = [(10*60+30, 11*60), (12*60, 12*60+30)]
    jacob_busy = [(9*60, 9*60+30), (10*60, 10*60+30), (11*60, 11*60+30), (12*60+30, 13*60+30), (14*60+30, 15*60)]
    stephen_busy = [(11*60+30, 12*60), (12*60+30, 13*60)]
    margaret_busy = [(9*60, 9*60+30), (10*60+30, 12*60+30), (13*60, 13*60+30), (15*60, 15*60+30), (16*60+30, 17*60)]
    mason_busy = [(9*60, 10*60), (10*60+30, 11*60), (11*60+30, 12*60+30), (13*60, 13*60+30), (14*60, 14*60+30), (16*60+30, 17*60)]
    
    # Combine all participants' busy slots
    all_busy = {
        'Shirley': shirley_busy,
        'Jacob': jacob_busy,
        'Stephen': stephen_busy,
        'Margaret': margaret_busy,
        'Mason': mason_busy
    }
    
    # For each participant, add constraints that the meeting does not overlap with any of their busy slots
    for participant, busy_slots in all_busy.items():
        for slot in busy_slots:
            slot_start, slot_end = slot
            # The meeting must either end before the slot starts or start after the slot ends
            s.add(Or(start + meeting_duration <= slot_start, start >= slot_end))
    
    # Check if a solution exists
    if s.check() == sat:
        model = s.model()
        start_minutes = model[start].as_long()
        # Convert start_minutes back to HH:MM format
        hours = start_minutes // 60
        minutes = start_minutes % 60
        start_str = f"{hours:02d}:{minutes:02d}"
        end_minutes = start_minutes + meeting_duration
        end_hours = end_minutes // 60
        end_minutes = end_minutes % 60
        end_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        # Output the solution
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()