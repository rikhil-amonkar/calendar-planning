from z3 import *
import json

def minutes_to_str(m):
    # Convert minutes since midnight to a HH:MM formatted string.
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def main():
    s = Solver()
    
    # We represent times in minutes since midnight.
    # Constants:
    # - Arrival at Castro at 9:00 → 540 minutes.
    # - Laura is available at Mission District from 12:15 (735) to 19:45 (1185).
    #   Minimum meeting time = 75 minutes.
    # - Anthony is available at Financial District from 12:30 (750) to 14:45 (885).
    #   Minimum meeting time = 30 minutes.
    
    # Define integer variables for the meeting start and end times.
    sAnthony = Int('sAnthony')
    eAnthony = Int('eAnthony')
    sLaura = Int('sLaura')
    eLaura = Int('eLaura')
    
    # Boolean variable to choose the order of meetings.
    # If orderAnFirst is True, we meet Anthony first (at Financial District)
    # then travel to Mission District to meet Laura.
    # Otherwise, we meet Laura first then Anthony.
    orderAnFirst = Bool('orderAnFirst')
    
    # Add availability and duration constraints.
    # Anthony constraints:
    s.add(sAnthony >= 750)        # Cannot start before his start time.
    s.add(eAnthony <= 885)          # Must finish by his end time.
    s.add(eAnthony - sAnthony >= 30)  # Meeting lasts at least 30 minutes.
    
    # Laura constraints:
    s.add(sLaura >= 735)          # Cannot start before her start time.
    s.add(eLaura <= 1185)         # Must finish by her end time.
    s.add(eLaura - sLaura >= 75)    # Meeting lasts at least 75 minutes.
    
    # For a clean “optimal” schedule we choose the minimum durations.
    s.add(eAnthony == sAnthony + 30)
    s.add(eLaura == sLaura + 75)
    
    # Travel times (in minutes):
    # From Castro: 
    #   To Mission District: 7 minutes.
    #   To Financial District: 20 minutes.
    # Between districts:
    #   From Financial District to Mission District: 17 minutes.
    #   From Mission District to Financial District: 17 minutes.
    
    # Case 1: Meet Anthony first (at Financial District) then Laura (at Mission District)
    # - Leaving Castro at 9:00, we must allow travel time from Castro to FD.
    #   (Travel time = 20 minutes; however, Anthony’s available time forces sAnthony >= 750.)
    # - After the Anthony meeting, travel from FD to Mission takes 17 minutes,
    #   so Laura’s meeting must start no earlier than eAnthony + 17.
    option1 = And(
        sAnthony >= 540 + 20,  # Castro -> Financial District.
        sLaura >= eAnthony + 17  # FD -> Mission District.
    )
    
    # Case 2: Meet Laura first then Anthony.
    # - From Castro to Mission District takes 7 minutes.
    # - Then must travel from Mission District to Financial District (17 minutes) before meeting Anthony.
    option2 = And(
        sLaura >= 540 + 7,      # Castro -> Mission District.
        sAnthony >= eLaura + 17 # Mission District -> Financial District.
    )
    
    # Choose the meeting order based on the Boolean variable.
    s.add(If(orderAnFirst, option1, option2))
    
    # To decide on a concrete schedule, we force the meeting order to be Anthony first.
    s.add(orderAnFirst == True)
    
    # Check for satisfiability and extract a solution.
    if s.check() == sat:
        m = s.model()
        anthony_start = m[sAnthony].as_long()
        anthony_end   = m[eAnthony].as_long()
        laura_start   = m[sLaura].as_long()
        laura_end     = m[eLaura].as_long()
        
        itinerary = [
            {"action": "meet", "person": "Anthony", "start_time": minutes_to_str(anthony_start), "end_time": minutes_to_str(anthony_end)},
            {"action": "meet", "person": "Laura", "start_time": minutes_to_str(laura_start), "end_time": minutes_to_str(laura_end)}
        ]
        
        # Output the itinerary as JSON.
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()