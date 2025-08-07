from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Define variables for each meeting's start and end times (in minutes since 9:00 AM)
    # Charles at Alamo Square (6:00 PM to 8:45 PM, min 90 mins)
    charles_start = Int('charles_start')
    charles_end = Int('charles_end')

    # Margaret at Russian Hill (9:00 AM to 4:00 PM, min 30 mins)
    margaret_start = Int('margaret_start')
    margaret_end = Int('margaret_end')

    # Daniel at Golden Gate Park (8:00 AM to 1:30 PM, min 15 mins)
    daniel_start = Int('daniel_start')
    daniel_end = Int('daniel_end')

    # Stephanie at Mission District (8:30 PM to 10:00 PM, min 90 mins)
    stephanie_start = Int('stephanie_start')
    stephanie_end = Int('stephanie_end')

    # Convert all times to minutes since 9:00 AM (540 minutes)
    # Charles: 6:00 PM is 1080 mins (18*60), 8:45 PM is 1125 mins
    s.add(charles_start >= 1080 - 540)  # 6:00 PM is 540 mins after 9:00 AM
    s.add(charles_end <= 1125 - 540)    # 8:45 PM is 585 mins after 9:00 AM
    s.add(charles_end - charles_start >= 90)

    # Margaret: 9:00 AM is 0 mins, 4:00 PM is 420 mins
    s.add(margaret_start >= 0)
    s.add(margaret_end <= 420)
    s.add(margaret_end - margaret_start >= 30)

    # Daniel: 8:00 AM is -60 mins, 1:30 PM is 270 mins
    s.add(daniel_start >= -60)
    s.add(daniel_end <= 270)
    s.add(daniel_end - daniel_start >= 15)

    # Stephanie: 8:30 PM is 690 mins, 10:00 PM is 780 mins
    s.add(stephanie_start >= 690 - 540)  # 8:30 PM is 690 mins after 9:00 AM (150 mins)
    s.add(stephanie_end <= 780 - 540)    # 10:00 PM is 780 mins after 9:00 AM (240 mins)
    s.add(stephanie_end - stephanie_start >= 90)

    # Define possible meeting orders
    # We'll try two different sequences to ensure we find a solution
    
    # Attempt 1: Daniel -> Margaret -> Charles -> Stephanie
    # Travel times:
    # Sunset to Golden Gate Park: 11 mins
    # Golden Gate Park to Russian Hill: 19 mins
    # Russian Hill to Alamo Square: 13 mins
    # Alamo Square to Mission District: 10 mins
    
    # Daniel first (Sunset to Golden Gate Park: 11 mins)
    s.add(daniel_start >= 11)
    # After Daniel, go to Margaret (Golden Gate Park to Russian Hill: 19 mins)
    s.add(margaret_start >= daniel_end + 19)
    # After Margaret, go to Charles (Russian Hill to Alamo Square: 13 mins)
    s.add(charles_start >= margaret_end + 13)
    # After Charles, go to Stephanie (Alamo Square to Mission District: 10 mins)
    s.add(stephanie_start >= charles_end + 10)

    # Add soft constraints to help the solver
    s.add_soft(charles_start == 540)  # Prefer to meet Charles right at 6:00 PM
    s.add_soft(stephanie_start == 690 - 540)  # Prefer to meet Stephanie right at 8:30 PM

    # Check if all meetings can fit
    if s.check() == sat:
        m = s.model()
        # Convert times back to HH:MM format
        def to_time(minutes):
            total_mins = 540 + minutes  # 9:00 AM is 540 mins
            h = total_mins // 60
            m = total_mins % 60
            return f"{h:02d}:{m:02d}"

        itinerary = [
            {"action": "meet", "person": "Daniel", "start_time": to_time(m[daniel_start].as_long()), "end_time": to_time(m[daniel_end].as_long())},
            {"action": "meet", "person": "Margaret", "start_time": to_time(m[margaret_start].as_long()), "end_time": to_time(m[margaret_end].as_long())},
            {"action": "meet", "person": "Charles", "start_time": to_time(m[charles_start].as_long()), "end_time": to_time(m[charles_end].as_long())},
            {"action": "meet", "person": "Stephanie", "start_time": to_time(m[stephanie_start].as_long()), "end_time": to_time(m[stephanie_end].as_long())}
        ]
        return {"itinerary": itinerary}
    else:
        # If first attempt fails, try alternative sequence
        s = Optimize()
        
        # Redefine variables and constraints
        charles_start = Int('charles_start2')
        charles_end = Int('charles_end2')
        margaret_start = Int('margaret_start2')
        margaret_end = Int('margaret_end2')
        daniel_start = Int('daniel_start2')
        daniel_end = Int('daniel_end2')
        stephanie_start = Int('stephanie_start2')
        stephanie_end = Int('stephanie_end2')

        # Same time window constraints as before
        s.add(charles_start >= 1080 - 540)
        s.add(charles_end <= 1125 - 540)
        s.add(charles_end - charles_start >= 90)
        
        s.add(margaret_start >= 0)
        s.add(margaret_end <= 420)
        s.add(margaret_end - margaret_start >= 30)
        
        s.add(daniel_start >= -60)
        s.add(daniel_end <= 270)
        s.add(daniel_end - daniel_start >= 15)
        
        s.add(stephanie_start >= 690 - 540)
        s.add(stephanie_end <= 780 - 540)
        s.add(stephanie_end - stephanie_start >= 90)

        # Alternative sequence: Margaret -> Daniel -> Charles -> Stephanie
        # Travel times:
        # Sunset to Russian Hill: 24 mins
        # Russian Hill to Golden Gate Park: 21 mins
        # Golden Gate Park to Alamo Square: 10 mins
        # Alamo Square to Mission District: 10 mins
        
        # Margaret first (Sunset to Russian Hill: 24 mins)
        s.add(margaret_start >= 24)
        # After Margaret, go to Daniel (Russian Hill to Golden Gate Park: 21 mins)
        s.add(daniel_start >= margaret_end + 21)
        # After Daniel, go to Charles (Golden Gate Park to Alamo Square: 10 mins)
        s.add(charles_start >= daniel_end + 10)
        # After Charles, go to Stephanie (Alamo Square to Mission District: 10 mins)
        s.add(stephanie_start >= charles_end + 10)

        if s.check() == sat:
            m = s.model()
            def to_time(minutes):
                total_mins = 540 + minutes
                h = total_mins // 60
                m = total_mins % 60
                return f"{h:02d}:{m:02d}"

            itinerary = [
                {"action": "meet", "person": "Margaret", "start_time": to_time(m[margaret_start].as_long()), "end_time": to_time(m[margaret_end].as_long())},
                {"action": "meet", "person": "Daniel", "start_time": to_time(m[daniel_start].as_long()), "end_time": to_time(m[daniel_end].as_long())},
                {"action": "meet", "person": "Charles", "start_time": to_time(m[charles_start].as_long()), "end_time": to_time(m[charles_end].as_long())},
                {"action": "meet", "person": "Stephanie", "start_time": to_time(m[stephanie_start].as_long()), "end_time": to_time(m[stephanie_end].as_long())}
            ]
            return {"itinerary": itinerary}
        else:
            return {"error": "No feasible schedule found after trying multiple sequences"}

# Run the solver
result = solve_scheduling()
print(result)