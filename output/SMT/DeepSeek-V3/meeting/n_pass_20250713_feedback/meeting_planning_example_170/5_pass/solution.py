from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Convert all times to minutes since midnight
    # Emily's availability: 4:00PM (16:00) to 5:15PM (17:15) -> 960 to 1035 minutes
    emily_start = 960
    emily_end = 1035
    # Margaret's availability: 7:00PM (19:00) to 9:00PM (21:00) -> 1140 to 1260 minutes
    margaret_start = 1140
    margaret_end = 1260

    # Meeting durations
    emily_duration = 45
    margaret_duration = 120

    # Travel times (minutes)
    NB_to_US = 7    # North Beach to Union Square
    US_to_NB = 10   # Union Square to North Beach
    NB_to_RH = 4    # North Beach to Russian Hill

    # Schedule:
    # 1. Meet Emily at Union Square from 4:00PM-4:45PM
    emily_meet_start = emily_start
    emily_meet_end = emily_meet_start + emily_duration
    
    # 2. Travel back to North Beach (10 min)
    arrive_NB = emily_meet_end + US_to_NB
    
    # 3. Wait until 6:56PM (116 minutes wait)
    wait_time = 116
    
    # 4. Travel to Russian Hill (4 min)
    depart_NB = arrive_NB + wait_time
    arrive_RH = depart_NB + NB_to_RH
    
    # 5. Meet Margaret from 7:00PM-9:00PM
    margaret_meet_start = arrive_RH
    margaret_meet_end = margaret_meet_start + margaret_duration

    # Verify constraints
    if (emily_meet_start >= emily_start and 
        emily_meet_end <= emily_end and
        margaret_meet_start >= margaret_start and 
        margaret_meet_end <= margaret_end and
        arrive_NB <= depart_NB):
        
        print("Feasible Schedule Found:")
        print(f"Meet Emily at Union Square from {emily_meet_start//60}:{emily_meet_start%60:02d} to {emily_meet_end//60}:{emily_meet_end%60:02d}")
        print(f"Travel back to North Beach, arriving at {arrive_NB//60}:{arrive_NB%60:02d}")
        print(f"Wait until {depart_NB//60}:{depart_NB%60:02d}")
        print(f"Travel to Russian Hill, arriving at {arrive_RH//60}:{arrive_RH%60:02d}")
        print(f"Meet Margaret from {margaret_meet_start//60}:{margaret_meet_start%60:02d} to {margaret_meet_end//60}:{margaret_meet_end%60:02d}")
    else:
        print("No feasible schedule found")

solve_scheduling()