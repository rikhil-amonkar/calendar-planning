from z3 import *

def main():
    # Travel times dictionary
    travel_times = {
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Richmond District"): 18
    }
    
    # Locations for each friend
    loc_Betty = "Presidio"
    loc_David = "Richmond District"
    loc_Barbara = "Fisherman's Wharf"
    
    # Availability windows (in minutes from 9:00 AM)
    betty_start = 75    # 10:15 AM
    betty_end = 750     # 9:30 PM
    david_start = 240   # 1:00 PM
    david_end = 675     # 8:15 PM
    barbara_start = 15  # 9:15 AM
    barbara_end = 675   # 8:15 PM
    
    # Minimum meeting durations
    dur_Betty = 45
    dur_David = 90
    dur_Barbara = 120
    
    # Initialize Z3 solver with optimization
    s = Optimize()
    
    # Boolean variables for meeting each friend
    meet_Betty = Bool('meet_Betty')
    meet_David = Bool('meet_David')
    meet_Barbara = Bool('meet_Barbara')
    
    # Start time variables (integers in minutes)
    S_Betty = Int('S_Betty')
    S_David = Int('S_David')
    S_Barbara = Int('S_Barbara')
    
    # Constraints for meeting Betty
    s.add(Implies(meet_Betty, And(
        S_Betty >= betty_start,
        S_Betty + dur_Betty <= betty_end,
        S_Betty >= travel_times[("Embarcadero", loc_Betty)]
    )))
    
    # Constraints for meeting David
    s.add(Implies(meet_David, And(
        S_David >= david_start,
        S_David + dur_David <= david_end,
        S_David >= travel_times[("Embarcadero", loc_David)]
    )))
    
    # Constraints for meeting Barbara
    s.add(Implies(meet_Barbara, And(
        S_Barbara >= barbara_start,
        S_Barbara + dur_Barbara <= barbara_end,
        S_Barbara >= travel_times[("Embarcadero", loc_Barbara)]
    )))
    
    # Pairwise constraints for Betty and David
    s.add(Implies(And(meet_Betty, meet_David), Or(
        S_David >= S_Betty + dur_Betty + travel_times[(loc_Betty, loc_David)],
        S_Betty >= S_David + dur_David + travel_times[(loc_David, loc_Betty)]
    ))
    
    # Pairwise constraints for Betty and Barbara
    s.add(Implies(And(meet_Betty, meet_Barbara), Or(
        S_Barbara >= S_Betty + dur_Betty + travel_times[(loc_Betty, loc_Barbara)],
        S_Betty >= S_Barbara + dur_Barbara + travel_times[(loc_Barbara, loc_Betty)]
    ))
    
    # Pairwise constraints for David and Barbara
    s.add(Implies(And(meet_David, meet_Barbara), Or(
        S_Barbara >= S_David + dur_David + travel_times[(loc_David, loc_Barbara)],
        S_David >= S_Barbara + dur_Barbara + travel_times[(loc_Barbara, loc_David)]
    ))
    
    # Maximize the number of friends met
    total_met = If(meet_Betty, 1, 0) + If(meet_David, 1, 0) + If(meet_Barbara, 1, 0)
    s.maximize(total_met)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Helper function to convert minutes to time string
        def minutes_to_time(minutes):
            total_minutes = minutes
            hours = total_minutes // 60
            minutes = total_minutes % 60
            am_pm = "AM" if hours < 12 else "PM"
            hours12 = hours % 12
            if hours12 == 0:
                hours12 = 12
            return f"{hours12}:{minutes:02d} {am_pm}"
        
        # Print which friends are met and their meeting times
        print("SOLUTION:")
        if m[meet_Betty]:
            start_time = m[S_Betty].as_long()
            end_time = start_time + dur_Betty
            print(f"Meet Betty at {loc_Betty} from {minutes_to_time(start_time)} to {minutes_to_time(end_time)}")
        if m[meet_David]:
            start_time = m[S_David].as_long()
            end_time = start_time + dur_David
            print(f"Meet David at {loc_David} from {minutes_to_time(start_time)} to {minutes_to_time(end_time)}")
        if m[meet_Barbara]:
            start_time = m[S_Barbara].as_long()
            end_time = start_time + dur_Barbara
            print(f"Meet Barbara at {loc_Barbara} from {minutes_to_time(start_time)} to {minutes_to_time(end_time)}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()