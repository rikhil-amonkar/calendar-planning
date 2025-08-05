from z3 import *
import json

def main():
    # Define travel times from Bayview to each location
    # Travel times between locations (asymmetric)
    travel_dict = {
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8,
        ('Financial District', 'Fisherman\'s Wharf'): 10,
        ('Financial District', 'Embarcadero'): 4,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Embarcadero', 'Financial District'): 5
    }
    
    # Initialize Z3 variables
    T_K = Int('T_K')  # Start time for meeting with Karen (in minutes)
    T_A = Int('T_A')  # Start time for meeting with Anthony
    T_B = Int('T_B')  # Start time for meeting with Betty
    KA = Bool('KA')   # True if Karen before Anthony
    KB = Bool('KB')   # True if Karen before Betty
    AB = Bool('AB')   # True if Anthony before Betty
    
    s = Solver()
    
    # Initial constraints: travel from Bayview to the first meeting
    s.add(T_K >= 540 + 25)  # Bayview to Fisherman's Wharf: 25 min
    s.add(T_A >= 540 + 19)  # Bayview to Financial District: 19 min
    s.add(T_B >= 540 + 19)  # Bayview to Embarcadero: 19 min
    
    # Availability constraints
    # Karen: available from 525 (8:45 AM) to 900 (3:00 PM)
    s.add(T_K >= 525, T_K + 30 <= 900)
    # Anthony: available from 555 (9:15 AM) to 1290 (9:30 PM)
    s.add(T_A >= 555, T_A + 105 <= 1290)
    # Betty: available from 1185 (7:45 PM) to 1305 (9:45 PM)
    s.add(T_B >= 1185, T_B + 15 <= 1305)
    
    # Pairwise constraints for meetings
    # Between Karen and Anthony
    s.add(If(KA, 
             T_A >= T_K + 30 + travel_dict[('Fisherman\'s Wharf', 'Financial District')],
             T_K >= T_A + 105 + travel_dict[('Financial District', 'Fisherman\'s Wharf')]
    ))
    
    # Between Karen and Betty
    s.add(If(KB,
             T_B >= T_K + 30 + travel_dict[('Fisherman\'s Wharf', 'Embarcadero')],
             T_K >= T_B + 15 + travel_dict[('Embarcadero', 'Fisherman\'s Wharf')]
    ))
    
    # Between Anthony and Betty
    s.add(If(AB,
             T_B >= T_A + 105 + travel_dict[('Financial District', 'Embarcadero')],
             T_A >= T_B + 15 + travel_dict[('Embarcadero', 'Financial District')]
    ))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        t_k = m.eval(T_K).as_long()
        t_a = m.eval(T_A).as_long()
        t_b = m.eval(T_B).as_long()
        
        # Prepare meetings list
        meetings = [
            {"person": "Karen", "start": t_k, "end": t_k + 30},
            {"person": "Anthony", "start": t_a, "end": t_a + 105},
            {"person": "Betty", "start": t_b, "end": t_b + 15}
        ]
        
        # Sort meetings by start time
        meetings.sort(key=lambda x: x["start"])
        
        # Format times to HH:MM
        def format_time(minutes):
            hours = minutes // 60
            minutes %= 60
            return f"{hours:02d}:{minutes:02d}"
        
        itinerary = []
        for meet in meetings:
            itinerary.append({
                "action": "meet",
                "person": meet["person"],
                "start_time": format_time(meet["start"]),
                "end_time": format_time(meet["end"])
            })
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()