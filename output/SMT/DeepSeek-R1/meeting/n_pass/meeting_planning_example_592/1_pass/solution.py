from z3 import *

def main():
    # Initialize the solver
    s = Optimize()
    
    # Define locations
    locations = [
        "North Beach",       # dummy (index0)
        "Pacific Heights",   # James (index1)
        "Chinatown",         # Robert (index2)
        "Union Square",      # Jeffrey (index3)
        "Mission District",  # Carol (index4)
        "Golden Gate Park",  # Mark (index5)
        "Nob Hill"           # Sandra (index6)
    ]
    
    # Travel time dictionary
    travel_time = {
        "North Beach": {
            "Pacific Heights": 8,
            "Chinatown": 6,
            "Union Square": 7,
            "Mission District": 18,
            "Golden Gate Park": 22,
            "Nob Hill": 7
        },
        "Pacific Heights": {
            "North Beach": 9,
            "Chinatown": 11,
            "Union Square": 12,
            "Mission District": 15,
            "Golden Gate Park": 15,
            "Nob Hill": 8
        },
        "Chinatown": {
            "North Beach": 3,
            "Pacific Heights": 10,
            "Union Square": 7,
            "Mission District": 18,
            "Golden Gate Park": 23,
            "Nob Hill": 8
        },
        "Union Square": {
            "North Beach": 10,
            "Pacific Heights": 15,
            "Chinatown": 7,
            "Mission District": 14,
            "Golden Gate Park": 22,
            "Nob Hill": 9
        },
        "Mission District": {
            "North Beach": 17,
            "Pacific Heights": 16,
            "Chinatown": 16,
            "Union Square": 15,
            "Golden Gate Park": 17,
            "Nob Hill": 12
        },
        "Golden Gate Park": {
            "North Beach": 24,
            "Pacific Heights": 16,
            "Chinatown": 23,
            "Union Square": 22,
            "Mission District": 17,
            "Nob Hill": 20
        },
        "Nob Hill": {
            "North Beach": 8,
            "Pacific Heights": 8,
            "Chinatown": 6,
            "Union Square": 7,
            "Mission District": 13,
            "Golden Gate Park": 17
        }
    }
    
    # Friend details (indices 1 to 6)
    friends_info = [
        {"name": "James", "avail_start": 20*60, "avail_end": 22*60, "min_duration": 120},
        {"name": "Robert", "avail_start": 12*60+15, "avail_end": 16*60+45, "min_duration": 90},
        {"name": "Jeffrey", "avail_start": 9*60+30, "avail_end": 15*60+30, "min_duration": 120},
        {"name": "Carol", "avail_start": 18*60+15, "avail_end": 21*60+15, "min_duration": 15},
        {"name": "Mark", "avail_start": 11*60+30, "avail_end": 17*60+45, "min_duration": 15},
        {"name": "Sandra", "avail_start": 8*60, "avail_end": 15*60+30, "min_duration": 15}
    ]
    
    # Create variables for meetings
    meet = [Bool(f"meet_{i}") for i in range(7)]  # 0 to 6
    start = [Int(f"start_{i}") for i in range(7)]
    end = [Int(f"end_{i}") for i in range(7)]
    
    # Dummy meeting (index0) at North Beach
    s.add(meet[0] == True)
    s.add(start[0] == 540)  # 9:00 AM
    s.add(end[0] == 540)
    
    # Constraints for each friend (indices 1 to 6)
    for i in range(1, 7):
        info = friends_info[i-1]
        s.add(Implies(meet[i],
              And(
                  start[i] >= info["avail_start"],
                  end[i] == start[i] + info["min_duration"],
                  end[i] <= info["avail_end"]
              )))
    
    # Pairwise constraints for travel times
    for i in range(7):
        for j in range(i+1, 7):
            loc_i = locations[i]
            loc_j = locations[j]
            time_ij = travel_time[loc_i][loc_j]
            time_ji = travel_time[loc_j][loc_i]
            s.add(Implies(And(meet[i], meet[j]),
                          Or(
                              start[j] >= end[i] + time_ij,
                              start[i] >= end[j] + time_ji
                          )))
    
    # Objective: maximize the number of friends met
    objective = Sum([If(meet[i], 1, 0) for i in range(1,7)])
    s.maximize(objective)
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(1,7):
            if is_true(m.evaluate(meet[i])):
                start_val = m.evaluate(start[i]).as_long()
                end_val = m.evaluate(end[i]).as_long()
                # Convert minutes to HH:MM format
                start_h = start_val // 60
                start_m = start_val % 60
                end_h = end_val // 60
                end_m = end_val % 60
                start_time = f"{start_h:02d}:{start_m:02d}"
                end_time = f"{end_h:02d}:{end_m:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": friends_info[i-1]["name"],
                    "start_time": start_time,
                    "end_time": end_time
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        result = {"itinerary": itinerary}
        print(f"SOLUTION: {result}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()