from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()

    # Define variables for meeting start and end times
    # Meeting with Timothy at Pacific Heights
    timothy_start = Int('timothy_start')
    timothy_end = Int('timothy_end')

    # Meeting with David at Fisherman's Wharf
    david_start = Int('david_start')
    david_end = Int('david_end')

    # Meeting with Robert at Mission District
    robert_start = Int('robert_start')
    robert_end = Int('robert_end')

    # Travel times (in minutes)
    # From Financial District to Pacific Heights: 13
    # From Pacific Heights to Fisherman's Wharf: 13
    # From Fisherman's Wharf to Mission District: 22
    # Alternatively, other routes could be considered, but we'll pick a feasible sequence.

    # Constraints for Timothy (Pacific Heights)
    s.add(timothy_start >= 9 * 60 + 0)  # 9:00 AM in minutes
    s.add(timothy_end <= 15 * 60 + 30)  # 3:30 PM in minutes
    s.add(timothy_end - timothy_start >= 75)  # 75 minutes meeting

    # Constraints for David (Fisherman's Wharf)
    s.add(david_start >= 10 * 60 + 45)  # 10:45 AM
    s.add(david_end <= 15 * 60 + 30)    # 3:30 PM
    s.add(david_end - david_start >= 15)  # 15 minutes meeting

    # Constraints for Robert (Mission District)
    s.add(robert_start >= 12 * 60 + 15)  # 12:15 PM
    s.add(robert_end <= 19 * 60 + 45)    # 7:45 PM (though we'll likely finish earlier)
    s.add(robert_end - robert_start >= 90)  # 90 minutes meeting

    # Arrival at Financial District at 9:00 AM (time = 9*60 = 540 minutes)

    # Assume the schedule is: Financial -> Pacific Heights -> Fisherman's Wharf -> Mission District
    # So the sequence is: 
    # 1. Travel to Pacific Heights (13 minutes), meet Timothy
    # 2. Travel to Fisherman's Wharf (13 minutes), meet David
    # 3. Travel to Mission District (22 minutes), meet Robert

    # Add travel and meeting sequence constraints
    s.add(timothy_start >= 9 * 60 + 13)  # arrive at Pacific Heights at 9:00 + 13 minutes travel
    s.add(david_start >= timothy_end + 13)  # travel from Pacific Heights to Fisherman's Wharf
    s.add(robert_start >= david_end + 22)  # travel from Fisherman's Wharf to Mission District

    # Check if all constraints can be satisfied
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        print(f"Meet Timothy at Pacific Heights from {m[timothy_start].as_long()//60}:{m[timothy_start].as_long()%60:02d} to {m[timothy_end].as_long()//60}:{m[timothy_end].as_long()%60:02d}")
        print(f"Meet David at Fisherman's Wharf from {m[david_start].as_long()//60}:{m[david_start].as_long()%60:02d} to {m[david_end].as_long()//60}:{m[david_end].as_long()%60:02d}")
        print(f"Meet Robert at Mission District from {m[robert_start].as_long()//60}:{m[robert_start].as_long()%60:02d} to {m[robert_end].as_long()//60}:{m[robert_end].as_long()%60:02d}")
    else:
        print("No feasible schedule found.")

solve_scheduling()