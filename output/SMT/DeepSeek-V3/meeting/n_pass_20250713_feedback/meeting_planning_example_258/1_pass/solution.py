from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()
    
    # Convert all times to minutes since 9:00 AM
    # Betty's availability: 10:15 AM to 9:30 PM -> 75 to 750 minutes
    betty_start_min = 75
    betty_end_min = 750
    
    # David's availability: 1:00 PM to 8:15 PM -> 240 to 555 minutes
    david_start_min = 240
    david_end_min = 555
    
    # Barbara's availability: 9:15 AM to 8:15 PM -> 15 to 555 minutes
    barbara_start_min = 15
    barbara_end_min = 555
    
    # Meeting durations in minutes
    betty_duration = 45
    david_duration = 90
    barbara_duration = 120
    
    # Travel times from each location to others (in minutes)
    # From Embarcadero (starting point)
    travel_emb_presidio = 20
    travel_emb_richmond = 21
    travel_emb_wharf = 6
    
    # From Presidio
    travel_presidio_emb = 20
    travel_presidio_richmond = 7
    travel_presidio_wharf = 19
    
    # From Richmond
    travel_richmond_emb = 19
    travel_richmond_presidio = 7
    travel_richmond_wharf = 18
    
    # From Fisherman's Wharf
    travel_wharf_emb = 8
    travel_wharf_presidio = 17
    travel_wharf_richmond = 18
    
    # Variables for meeting start and end times
    # Betty (Presidio)
    betty_start = Int('betty_start')
    betty_end = Int('betty_end')
    
    # David (Richmond)
    david_start = Int('david_start')
    david_end = Int('david_end')
    
    # Barbara (Fisherman's Wharf)
    barbara_start = Int('barbara_start')
    barbara_end = Int('barbara_end')
    
    # Constraints for meeting durations
    s.add(betty_end == betty_start + betty_duration)
    s.add(david_end == david_start + david_duration)
    s.add(barbara_end == barbara_start + barbara_duration)
    
    # Constraints for availability windows
    s.add(betty_start >= betty_start_min)
    s.add(betty_end <= betty_end_min)
    
    s.add(david_start >= david_start_min)
    s.add(david_end <= david_end_min)
    
    s.add(barbara_start >= barbara_start_min)
    s.add(barbara_end <= barbara_end_min)
    
    # Variables to track the order of meetings and travel times
    # We need to model the sequence of meetings and ensure travel times are respected.
    # There are 3! = 6 possible orders. We'll model all possibilities and let Z3 choose.
    
    # We'll use auxiliary variables to represent the order.
    # Let’s define variables for the order (0: Barbara first, 1: Betty first, 2: David first)
    # Then, we'll have constraints for each possible order.
    
    # We'll create a variable to represent the order.
    order = Int('order')
    s.add(order >= 0, order <= 5)  # 6 possible permutations
    
    # Barbara (Bara), Betty (Bet), David (Dav)
    # Possible orders:
    # 0: Bara -> Bet -> Dav
    # 1: Bara -> Dav -> Bet
    # 2: Bet -> Bara -> Dav
    # 3: Bet -> Dav -> Bara
    # 4: Dav -> Bara -> Bet
    # 5: Dav -> Bet -> Bara
    
    # Constraints for each order:
    
    # Order 0: Bara -> Bet -> Dav
    s.add(Implies(order == 0,
                  And(barbara_end + travel_wharf_presidio <= betty_start,
                      betty_end + travel_presidio_richmond <= david_start)))
    
    # Order 1: Bara -> Dav -> Bet
    s.add(Implies(order == 1,
                  And(barbara_end + travel_wharf_richmond <= david_start,
                      david_end + travel_richmond_presidio <= betty_start)))
    
    # Order 2: Bet -> Bara -> Dav
    s.add(Implies(order == 2,
                  And(betty_end + travel_presidio_wharf <= barbara_start,
                      barbara_end + travel_wharf_richmond <= david_start)))
    
    # Order 3: Bet -> Dav -> Bara
    s.add(Implies(order == 3,
                  And(betty_end + travel_presidio_richmond <= david_start,
                      david_end + travel_richmond_wharf <= barbara_start)))
    
    # Order 4: Dav -> Bara -> Bet
    s.add(Implies(order == 4,
                  And(david_end + travel_richmond_wharf <= barbara_start,
                      barbara_end + travel_wharf_presidio <= betty_start)))
    
    # Order 5: Dav -> Bet -> Bara
    s.add(Implies(order == 5,
                  And(david_end + travel_richmond_presidio <= betty_start,
                      betty_end + travel_presidio_wharf <= barbara_start)))
    
    # Also, the first meeting must start after travel from Embarcadero.
    # For Barbara first:
    s.add(Implies(Or(order == 0, order == 1, order == 4, order == 5),
                  barbara_start >= travel_emb_wharf))
    # For Betty first:
    s.add(Implies(Or(order == 2, order == 3),
                  betty_start >= travel_emb_presidio))
    # For David first:
    # Not possible since David's availability starts at 1 PM, and we start at 9 AM.
    # So orders where David is first (4,5) would require starting after travel to Richmond (21 minutes), but David's window starts at 240 minutes (1 PM).
    # So these orders are feasible, but the first meeting would start at 1 PM.
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        # Get the order
        ord_val = m.evaluate(order).as_long()
        # Print the order
        order_names = [
            "Barbara -> Betty -> David",
            "Barbara -> David -> Betty",
            "Betty -> Barbara -> David",
            "Betty -> David -> Barbara",
            "David -> Barbara -> Betty",
            "David -> Betty -> Barbara"
        ]
        print("Meeting order:", order_names[ord_val])
        
        # Convert times back to HH:MM format
        def minutes_to_time(minutes):
            hours = (minutes) // 60
            mins = (minutes) % 60
            return f"{9 + hours}:{mins:02d}"
        
        # Print meeting times
        barbara_start_time = m.evaluate(barbara_start).as_long()
        barbara_end_time = m.evaluate(barbara_end).as_long()
        print(f"Meet Barbara at Fisherman's Wharf from {minutes_to_time(barbara_start_time)} to {minutes_to_time(barbara_end_time)}")
        
        betty_start_time = m.evaluate(betty_start).as_long()
        betty_end_time = m.evaluate(betty_end).as_long()
        print(f"Meet Betty at Presidio from {minutes_to_time(betty_start_time)} to {minutes_to_time(betty_end_time)}")
        
        david_start_time = m.evaluate(david_start).as_long()
        david_end_time = m.evaluate(david_end).as_long()
        print(f"Meet David at Richmond District from {minutes_to_time(david_start_time)} to {minutes_to_time(david_end_time)}")
    else:
        print("No feasible schedule found.")

solve_scheduling()