from z3 import *
import json

def main():
    # Meetings info: (index, name, location, available_start_min, available_end_min, duration_min)
    meetings_info = [
        (1, "Kevin", "Mission District", 705, 765, 60),      # 8:45 PM to 9:45 PM
        (2, "Mark", "Fisherman's Wharf", 495, 660, 90),      # 5:15 PM to 8:00 PM
        (3, "Jessica", "Russian Hill", 0, 360, 120),         # 9:00 AM to 3:00 PM
        (4, "Jason", "Marina District", 375, 765, 120),      # 3:15 PM to 9:45 PM
        (5, "John", "North Beach", 45, 540, 15),             # 9:45 AM to 6:00 PM
        (6, "Karen", "Chinatown", 465, 600, 75),             # 4:45 PM to 7:00 PM
        (7, "Sarah", "Pacific Heights", 510, 555, 45),       # 5:30 PM to 6:15 PM
        (8, "Amanda", "The Castro", 660, 735, 60),           # 8:00 PM to 9:15 PM
        (9, "Nancy", "Nob Hill", 45, 240, 45),               # 9:45 AM to 1:00 PM
        (10, "Rebecca", "Sunset District", -15, 360, 75)     # 8:45 AM to 3:00 PM
    ]
    
    # Travel times dictionary: (from_location, to_location) -> minutes
    travel_dict = {
        ("Union Square", "Mission District"): 14,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Pacific Heights"): 15,
        ("Union Square", "The Castro"): 17,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Sunset District"): 27,
        ("Mission District", "Union Square"): 15,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Russian Hill"): 15,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "Chinatown"): 16,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Sunset District"): 24,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Fisherman's Wharf", "Chinatown"): 12,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "The Castro"): 27,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Mission District"): 16,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "Sunset District"): 23,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Sunset District"): 19,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Mission District"): 18,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "The Castro"): 23,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Sunset District"): 27,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Mission District"): 17,
        ("Chinatown", "Fisherman's Wharf"): 8,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "The Castro"): 22,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Sunset District"): 29,
        ("Pacific Heights", "Union Square"): 12,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Sunset District"): 21,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Chinatown"): 22,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Sunset District"): 17,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Mission District"): 13,
        ("Nob Hill", "Fisherman's Wharf"): 10,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Sunset District"): 24,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Mission District"): 25,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "North Beach"): 28,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "Pacific Heights"): 21,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Nob Hill"): 27
    }
    
    # Location of the dummy meeting (index0) is Union Square
    dummy_location = "Union Square"
    
    # Create solver
    s = Solver()
    
    n_real_meetings = len(meetings_info)
    meet_vars = [Bool(f"meet_{i}") for i in range(n_real_meetings)]
    start_vars = [Int(f"start_{i}") for i in range(n_real_meetings)]
    end_vars = [Int(f"end_{i}") for i in range(n_real_meetings)]
    
    # Constraints for each real meeting
    for i in range(n_real_meetings):
        idx, name, loc, avail_start, avail_end, dur = meetings_info[i]
        # Travel time from Union Square (dummy) to this meeting's location
        travel_time0 = travel_dict.get((dummy_location, loc))
        if travel_time0 is None:
            print(f"Travel time not found from Union Square to {loc}")
            travel_time0 = 0
        
        # Add constraints if meeting is scheduled
        s.add(Implies(meet_vars[i], start_vars[i] >= travel_time0))
        s.add(Implies(meet_vars[i], start_vars[i] >= avail_start))
        s.add(Implies(meet_vars[i], end_vars[i] == start_vars[i] + dur))
        s.add(Implies(meet_vars[i], end_vars[i] <= avail_end))
    
    # Order variables for every pair of real meetings (i < j)
    order_vars = {}
    for i in range(n_real_meetings):
        for j in range(i+1, n_real_meetings):
            order_vars[(i, j)] = Bool(f"order_{i}_{j}")
    
    # Constraints for every pair of meetings
    for i in range(n_real_meetings):
        for j in range(i+1, n_real_meetings):
            loc_i = meetings_info[i][2]
            loc_j = meetings_info[j][2]
            travel_ij = travel_dict.get((loc_i, loc_j))
            travel_ji = travel_dict.get((loc_j, loc_i))
            if travel_ij is None or travel_ji is None:
                continue
            # If both meetings are scheduled, enforce travel time and order
            s.add(Implies(And(meet_vars[i], meet_vars[j]),
                Or(
                    And(order_vars[(i, j)], start_vars[j] >= end_vars[i] + travel_ij),
                    And(Not(order_vars[(i, j)]), start_vars[i] >= end_vars[j] + travel_ji)
                )))
    
    # Maximize the number of meetings
    objective = Sum([If(meet_vars[i], 1, 0) for i in range(n_real_meetings)])
    s.maximize(objective)
    
    # Check and get solution
    if s.check() == sat:
        m = s.model()
        scheduled_meetings = []
        for i in range(n_real_meetings):
            if m.evaluate(meet_vars[i]):
                start_val = m.evaluate(start_vars[i])
                end_val = m.evaluate(end_vars[i])
                if is_int_value(start_val) and is_int_value(end_val):
                    start_min = start_val.as_long()
                    end_min = end_val.as_long()
                    # Convert to time string
                    start_hour = 9 + start_min // 60
                    start_minute = start_min % 60
                    end_hour = 9 + end_min // 60
                    end_minute = end_min % 60
                    start_time = f"{start_hour:02d}:{start_minute:02d}"
                    end_time = f"{end_hour:02d}:{end_minute:02d}"
                    name = meetings_info[i][1]
                    scheduled_meetings.append({
                        "action": "meet",
                        "person": name,
                        "start_time": start_time,
                        "end_time": end_time
                    })
        # Sort by start time
        scheduled_meetings.sort(key=lambda x: x['start_time'])
        result = {"itinerary": scheduled_meetings}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

def is_int_value(v):
    return isinstance(v, IntNumRef)

if __name__ == "__main__":
    main()