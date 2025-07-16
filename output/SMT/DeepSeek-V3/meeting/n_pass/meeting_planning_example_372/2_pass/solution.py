from z3 import *

def solve_scheduling():
    s = Solver()

    # Time is in minutes since midnight
    # Define variables for each meeting's start and end times
    margaret_start = Int('margaret_start')
    margaret_end = Int('margaret_end')
    
    daniel_start = Int('daniel_start')
    daniel_end = Int('daniel_end')
    
    charles_start = Int('charles_start')
    charles_end = Int('charles_end')
    
    stephanie_start = Int('stephanie_start')
    stephanie_end = Int('stephanie_end')

    # Arrival at Sunset District at 9:00AM (540 minutes since midnight)
    start_time = 540

    # Constraints for Margaret (Russian Hill: 9:00AM-4:00PM, min 30 mins)
    s.add(margaret_start >= start_time + 24)  # Travel from Sunset to Russian Hill: 24 mins
    s.add(margaret_start >= 540)  # Available from 9:00AM (540)
    s.add(margaret_end == margaret_start + 30)
    s.add(margaret_end <= 960)  # 4:00PM is 960 minutes since midnight

    # Constraints for Daniel (Golden Gate Park: 8:00AM-1:30PM, min 15 mins)
    s.add(daniel_start >= start_time + 11)  # Travel from Sunset to Golden Gate Park: 11 mins
    s.add(daniel_start >= 480)  # Available from 8:00AM (480)
    s.add(daniel_end == daniel_start + 15)
    s.add(daniel_end <= 810)  # 1:30PM is 810 minutes since midnight

    # Constraints for Charles (Alamo Square: 6:00PM-8:45PM, min 90 mins)
    s.add(charles_start >= 1080)  # Available from 6:00PM (1080)
    s.add(charles_end == charles_start + 90)
    s.add(charles_end <= 1125)  # 8:45PM is 1125 minutes since midnight

    # Constraints for Stephanie (Mission District: 8:30PM-10:00PM, min 90 mins)
    s.add(stephanie_start >= 1230)  # Available from 8:30PM (1230)
    s.add(stephanie_end == stephanie_start + 90)
    s.add(stephanie_end <= 1260)  # 10:00PM is 1260 minutes since midnight

    # Travel constraints between meetings
    # Assume the order is Daniel -> Margaret -> Charles -> Stephanie
    s.add(daniel_start >= start_time + 11)  # Sunset to Golden Gate Park: 11 mins
    s.add(margaret_start >= daniel_end + 19)  # Golden Gate Park to Russian Hill: 19 mins
    s.add(charles_start >= margaret_end + 15)  # Russian Hill to Alamo Square: 15 mins
    s.add(stephanie_start >= charles_end + 10)  # Alamo Square to Mission District: 10 mins

    # Check if the schedule is feasible
    if s.check() == sat:
        m = s.model()
        print("Feasible schedule found:")
        # Convert times back to hours for readability
        def minutes_to_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours}:{mins:02d}"

        daniel_start_time = m[daniel_start].as_long()
        daniel_end_time = m[daniel_end].as_long()
        print(f"Meet Daniel at Golden Gate Park from {minutes_to_time(daniel_start_time)} to {minutes_to_time(daniel_end_time)}")

        margaret_start_time = m[margaret_start].as_long()
        margaret_end_time = m[margaret_end].as_long()
        print(f"Meet Margaret at Russian Hill from {minutes_to_time(margaret_start_time)} to {minutes_to_time(margaret_end_time)}")

        charles_start_time = m[charles_start].as_long()
        charles_end_time = m[charles_end].as_long()
        print(f"Meet Charles at Alamo Square from {minutes_to_time(charles_start_time)} to {minutes_to_time(charles_end_time)}")

        stephanie_start_time = m[stephanie_start].as_long()
        stephanie_end_time = m[stephanie_end].as_long()
        print(f"Meet Stephanie at Mission District from {minutes_to_time(stephanie_start_time)} to {minutes_to_time(stephanie_end_time)}")
    else:
        print("No feasible schedule found to meet all friends.")

solve_scheduling()