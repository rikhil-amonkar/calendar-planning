from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for each meeting's start and end times (in minutes since 9:00 AM)
    # Convert all times to minutes from 9:00 AM (540 minutes from midnight)
    # Russian Hill arrival time: 0 minutes (since it's 9:00 AM)
    
    # Meeting with Timothy at Embarcadero
    timothy_start = Int('timothy_start')
    timothy_end = Int('timothy_end')
    # Timothy's availability: 9:45 AM (45 mins) to 5:45 PM (17*60 + 45 = 1065 mins)
    timothy_available_start = 45  # 9:45 AM is 45 mins after 9:00 AM
    timothy_available_end = 1065   # 5:45 PM is 1065 mins after 9:00 AM (17*60 +45)
    
    # Meeting with Ashley at Mission District
    ashley_start = Int('ashley_start')
    ashley_end = Int('ashley_end')
    # Ashley's availability: 8:30 PM (20*60 +30 = 1230 mins) to 9:15 PM (21*60 +15 = 1275 mins)
    ashley_available_start = 1230 - 540  # 690 mins after 9:00 AM
    ashley_available_end = 1275 - 540    # 735 mins after 9:00 AM
    
    # Meeting with Patricia at Nob Hill
    patricia_start = Int('patricia_start')
    patricia_end = Int('patricia_end')
    # Patricia's availability: 6:30 PM (18*60 +30 = 1110 mins) to 9:45 PM (21*60 +45 = 1305 mins)
    patricia_available_start = 1110 - 540  # 570 mins after 9:00 AM
    patricia_available_end = 1305 - 540    # 765 mins after 9:00 AM

    # Add constraints for each meeting's duration and availability
    # Timothy: at least 120 minutes
    s.add(timothy_start >= timothy_available_start)
    s.add(timothy_end <= timothy_available_end)
    s.add(timothy_end - timothy_start >= 120)
    
    # Ashley: at least 45 minutes
    s.add(ashley_start >= ashley_available_start)
    s.add(ashley_end <= ashley_available_end)
    s.add(ashley_end - ashley_start >= 45)
    
    # Patricia: at least 90 minutes
    s.add(patricia_start >= patricia_available_start)
    s.add(patricia_end <= patricia_available_end)
    s.add(patricia_end - patricia_start >= 90)

    # Current location starts at Russian Hill (time 0)
    # Define travel times
    travel = {
        ('Russian Hill', 'Nob Hill'): 5,
        ('Russian Hill', 'Mission District'): 16,
        ('Russian Hill', 'Embarcadero'): 8,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'Mission District'): 13,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Mission District', 'Russian Hill'): 15,
        ('Mission District', 'Nob Hill'): 12,
        ('Mission District', 'Embarcadero'): 19,
        ('Embarcadero', 'Russian Hill'): 8,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Mission District'): 20,
    }

    # Define the order of meetings and travels
    # We need to sequence the meetings: possibly Timothy first, then Ashley, then Patricia
    # Or other orders. We'll try to find a feasible sequence.

    # Option 1: Timothy -> Ashley -> Patricia
    # Travel from Russian Hill to Embarcadero: 8 mins
    s.add(timothy_start >= 8)  # start after travel
    
    # Travel from Embarcadero to Mission District: 20 mins
    # So ashley_start >= timothy_end + 20
    s.add(ashley_start >= timothy_end + 20)
    
    # Travel from Mission District to Nob Hill: 12 mins
    # So patricia_start >= ashley_end + 12
    s.add(patricia_start >= ashley_end + 12)
    
    # Check if this sequence is possible
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print("Meeting Timothy at Embarcadero from", 
              convert_to_time(m[timothy_start].as_long()), 
              "to", convert_to_time(m[timothy_end].as_long()))
        print("Travel to Mission District, arriving by", 
              convert_to_time(m[ashley_start].as_long()))
        print("Meeting Ashley at Mission District from", 
              convert_to_time(m[ashley_start].as_long()), 
              "to", convert_to_time(m[ashley_end].as_long()))
        print("Travel to Nob Hill, arriving by", 
              convert_to_time(m[patricia_start].as_long()))
        print("Meeting Patricia at Nob Hill from", 
              convert_to_time(m[patricia_start].as_long()), 
              "to", convert_to_time(m[patricia_end].as_long()))
        return

    # If Option 1 doesn't work, try another sequence
    s.reset()
    s = Solver()

    # Re-add the meeting constraints
    s.add(timothy_start >= timothy_available_start)
    s.add(timothy_end <= timothy_available_end)
    s.add(timothy_end - timothy_start >= 120)
    
    s.add(ashley_start >= ashley_available_start)
    s.add(ashley_end <= ashley_available_end)
    s.add(ashley_end - ashley_start >= 45)
    
    s.add(patricia_start >= patricia_available_start)
    s.add(patricia_end <= patricia_available_end)
    s.add(patricia_end - patricia_start >= 90)

    # Option 2: Timothy -> Patricia -> Ashley
    # Travel Russian Hill to Embarcadero: 8 mins
    s.add(timothy_start >= 8)
    
    # Travel Embarcadero to Nob Hill: 10 mins
    s.add(patricia_start >= timothy_end + 10)
    
    # Travel Nob Hill to Mission District: 13 mins
    s.add(ashley_start >= patricia_end + 13)
    
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print("Meeting Timothy at Embarcadero from", 
              convert_to_time(m[timothy_start].as_long()), 
              "to", convert_to_time(m[timothy_end].as_long()))
        print("Travel to Nob Hill, arriving by", 
              convert_to_time(m[patricia_start].as_long()))
        print("Meeting Patricia at Nob Hill from", 
              convert_to_time(m[patricia_start].as_long()), 
              "to", convert_to_time(m[patricia_end].as_long()))
        print("Travel to Mission District, arriving by", 
              convert_to_time(m[ashley_start].as_long()))
        print("Meeting Ashley at Mission District from", 
              convert_to_time(m[ashley_start].as_long()), 
              "to", convert_to_time(m[ashley_end].as_long()))
        return

    # If neither sequence works, try another
    s.reset()
    s = Solver()

    s.add(timothy_start >= timothy_available_start)
    s.add(timothy_end <= timothy_available_end)
    s.add(timothy_end - timothy_start >= 120)
    
    s.add(ashley_start >= ashley_available_start)
    s.add(ashley_end <= ashley_available_end)
    s.add(ashley_end - ashley_start >= 45)
    
    s.add(patricia_start >= patricia_available_start)
    s.add(patricia_end <= patricia_available_end)
    s.add(patricia_end - patricia_start >= 90)

    # Option 3: Patricia -> Ashley -> Timothy (but Timothy's window is earlier)
    # This likely won't work, but just for completeness
    # Travel Russian Hill to Nob Hill: 5 mins
    s.add(patricia_start >= 5)
    
    # Travel Nob Hill to Mission District: 13 mins
    s.add(ashley_start >= patricia_end + 13)
    
    # Travel Mission District to Embarcadero: 19 mins
    s.add(timothy_start >= ashley_end + 19)
    
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print("Meeting Patricia at Nob Hill from", 
              convert_to_time(m[patricia_start].as_long()), 
              "to", convert_to_time(m[patricia_end].as_long()))
        print("Travel to Mission District, arriving by", 
              convert_to_time(m[ashley_start].as_long()))
        print("Meeting Ashley at Mission District from", 
              convert_to_time(m[ashley_start].as_long()), 
              "to", convert_to_time(m[ashley_end].as_long()))
        print("Travel to Embarcadero, arriving by", 
              convert_to_time(m[timothy_start].as_long()))
        print("Meeting Timothy at Embarcadero from", 
              convert_to_time(m[timothy_start].as_long()), 
              "to", convert_to_time(m[timothy_end].as_long()))
        return

    print("No feasible schedule found.")

def convert_to_time(minutes):
    # Convert minutes since 9:00 AM back to HH:MM format
    total_minutes = 540 + minutes  # 9:00 AM is 540 minutes since midnight
    hours = total_minutes // 60
    mins = total_minutes % 60
    return f"{hours}:{mins:02d}"

solve_scheduling()