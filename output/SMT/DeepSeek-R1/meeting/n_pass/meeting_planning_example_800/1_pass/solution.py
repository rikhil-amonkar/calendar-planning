from z3 import *
import json

def main():
    # Define friends data
    friends = [
        {"name": "Melissa", "loc": "The Castro", "start_avail": 20*60+15, "end_avail": 21*60+15, "min_dur": 30},
        {"name": "Kimberly", "loc": "North Beach", "start_avail": 7*60, "end_avail": 10*60+30, "min_dur": 15},
        {"name": "Joseph", "loc": "Embarcadero", "start_avail": 15*60+30, "end_avail": 19*60+30, "min_dur": 75},
        {"name": "Barbara", "loc": "Alamo Square", "start_avail": 20*60+45, "end_avail": 21*60+45, "min_dur": 15},
        {"name": "Kenneth", "loc": "Nob Hill", "start_avail": 12*60+15, "end_avail": 17*60+15, "min_dur": 105},
        {"name": "Joshua", "loc": "Presidio", "start_avail": 16*60+30, "end_avail": 18*60+15, "min_dur": 105},
        {"name": "Brian", "loc": "Fisherman's Wharf", "start_avail": 9*60+30, "end_avail": 15*60+30, "min_dur": 45},
        {"name": "Steven", "loc": "Mission District", "start_avail": 19*60+30, "end_avail": 21*60, "min_dur": 90},
        {"name": "Betty", "loc": "Haight-Ashbury", "start_avail": 19*60, "end_avail": 20*60+30, "min_dur": 90}
    ]
    
    # Define travel_time dictionary
    travel_time = {
        "Union Square": {
            "The Castro": 17,
            "North Beach": 10,
            "Embarcadero": 11,
            "Alamo Square": 15,
            "Nob Hill": 9,
            "Presidio": 24,
            "Fisherman's Wharf": 15,
            "Mission District": 14,
            "Haight-Ashbury": 18
        },
        "The Castro": {
            "Union Square": 19,
            "North Beach": 20,
            "Embarcadero": 22,
            "Alamo Square": 8,
            "Nob Hill": 16,
            "Presidio": 20,
            "Fisherman's Wharf": 24,
            "Mission District": 7,
            "Haight-Ashbury": 6
        },
        "North Beach": {
            "Union Square": 7,
            "The Castro": 23,
            "Embarcadero": 6,
            "Alamo Square": 16,
            "Nob Hill": 7,
            "Presidio": 17,
            "Fisherman's Wharf": 5,
            "Mission District": 18,
            "Haight-Ashbury": 18
        },
        "Embarcadero": {
            "Union Square": 10,
            "The Castro": 25,
            "North Beach": 5,
            "Alamo Square": 19,
            "Nob Hill": 10,
            "Presidio": 20,
            "Fisherman's Wharf": 6,
            "Mission District": 20,
            "Haight-Ashbury": 21
        },
        "Alamo Square": {
            "Union Square": 14,
            "The Castro": 8,
            "North Beach": 15,
            "Embarcadero": 16,
            "Nob Hill": 11,
            "Presidio": 17,
            "Fisherman's Wharf": 19,
            "Mission District": 10,
            "Haight-Ashbury": 5
        },
        "Nob Hill": {
            "Union Square": 7,
            "The Castro": 17,
            "North Beach": 8,
            "Embarcadero": 9,
            "Alamo Square": 11,
            "Presidio": 17,
            "Fisherman's Wharf": 10,
            "Mission District": 13,
            "Haight-Ashbury": 13
        },
        "Presidio": {
            "Union Square": 22,
            "The Castro": 21,
            "North Beach": 18,
            "Embarcadero": 20,
            "Alamo Square": 19,
            "Nob Hill": 18,
            "Fisherman's Wharf": 19,
            "Mission District": 26,
            "Haight-Ashbury": 15
        },
        "Fisherman's Wharf": {
            "Union Square": 13,
            "The Castro": 27,
            "North Beach": 6,
            "Embarcadero": 8,
            "Alamo Square": 21,
            "Nob Hill": 11,
            "Presidio": 17,
            "Mission District": 22,
            "Haight-Ashbury": 22
        },
        "Mission District": {
            "Union Square": 15,
            "The Castro": 7,
            "North Beach": 17,
            "Embarcadero": 19,
            "Alamo Square": 11,
            "Nob Hill": 12,
            "Presidio": 25,
            "Fisherman's Wharf": 22,
            "Haight-Ashbury": 12
        },
        "Haight-Ashbury": {
            "Union Square": 19,
            "The Castro": 6,
            "North Beach": 19,
            "Embarcadero": 20,
            "Alamo Square": 5,
            "Nob Hill": 15,
            "Presidio": 15,
            "Fisherman's Wharf": 23,
            "Mission District": 11
        }
    }
    
    # Create Z3 variables
    n = 9  # number of friends
    meet = [Bool(f"meet_{i}") for i in range(n)]
    start = [Int(f"start_{i}") for i in range(n+1)]  # indices 0 to n; 0 is dummy
    end = [Int(f"end_{i}") for i in range(n+1)]
    
    s = Optimize()
    
    # Dummy meeting at Union Square: 9:00 AM (540 minutes)
    s.add(start[0] == 540)
    s.add(end[0] == 540)
    
    # Constraints for each friend
    for i in range(n):
        loc = friends[i]["loc"]
        start_avail = friends[i]["start_avail"]
        end_avail = friends[i]["end_avail"]
        min_dur = friends[i]["min_dur"]
        
        # If we meet the friend, then:
        #   start[i+1] >= 540 + travel_time from Union Square to loc
        s.add(Implies(meet[i], start[i+1] >= 540 + travel_time["Union Square"][loc]))
        s.add(Implies(meet[i], start[i+1] >= start_avail))
        s.add(Implies(meet[i], end[i+1] == start[i+1] + min_dur))
        s.add(Implies(meet[i], end[i+1] <= end_avail))
    
    # Pairwise constraints for real meetings
    for i in range(n):
        for j in range(i+1, n):
            loc_i = friends[i]["loc"]
            loc_j = friends[j]["loc"]
            travel_ij = travel_time[loc_i][loc_j]
            travel_ji = travel_time[loc_j][loc_i]
            
            s.add(Implies(And(meet[i], meet[j]),
                             Or( end[i+1] + travel_ij <= start[j+1], 
                                 end[j+1] + travel_ji <= start[i+1] ) 
                        ))
    
    # Maximize the number of friends met
    s.maximize(Sum([If(meet[i], 1, 0) for i in range(n)]))
    
    # Check and get the model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(n):
            if model.evaluate(meet[i]):
                start_val = model.evaluate(start[i+1])
                end_val = model.evaluate(end[i+1])
                # Convert to integers
                if is_int_value(start_val) and is_int_value(end_val):
                    start_min = start_val.as_long()
                    end_min = end_val.as_long()
                    start_hour = start_min // 60
                    start_minute = start_min % 60
                    end_hour = end_min // 60
                    end_minute = end_min % 60
                    start_str = f"{start_hour:02d}:{start_minute:02d}"
                    end_str = f"{end_hour:02d}:{end_minute:02d}"
                    itinerary.append({
                        "action": "meet",
                        "person": friends[i]["name"],
                        "start_time": start_str,
                        "end_time": end_str
                    })
        
        # Sort itinerary by start time
        itinerary_sorted = sorted(itinerary, key=lambda x: x["start_time"])
        print('SOLUTION:')
        print(json.dumps({"itinerary": itinerary_sorted}))
    else:
        print("No solution found")

def is_int_value(v):
    return isinstance(v, IntNumRef)

if __name__ == "__main__":
    main()