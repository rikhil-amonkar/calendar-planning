from z3 import *

def main():
    # Define travel times between districts
    travel_dict = {
        "Marina District": {
            "Embarcadero": 14, "Bayview": 27, "Union Square": 16, "Chinatown": 15, "Sunset District": 19,
            "Golden Gate Park": 18, "Financial District": 17, "Haight-Ashbury": 16, "Mission District": 20
        },
        "Embarcadero": {
            "Marina District": 12, "Bayview": 21, "Union Square": 10, "Chinatown": 7, "Sunset District": 30,
            "Golden Gate Park": 25, "Financial District": 5, "Haight-Ashbury": 21, "Mission District": 20
        },
        "Bayview": {
            "Marina District": 27, "Embarcadero": 19, "Union Square": 18, "Chinatown": 19, "Sunset District": 23,
            "Golden Gate Park": 22, "Financial District": 19, "Haight-Ashbury": 19, "Mission District": 13
        },
        "Union Square": {
            "Marina District": 18, "Embarcadero": 11, "Bayview": 15, "Chinatown": 7, "Sunset District": 27,
            "Golden Gate Park": 22, "Financial District": 9, "Haight-Ashbury": 18, "Mission District": 14
        },
        "Chinatown": {
            "Marina District": 12, "Embarcadero": 5, "Bayview": 20, "Union Square": 7, "Sunset District": 29,
            "Golden Gate Park": 23, "Financial District": 5, "Haight-Ashbury": 19, "Mission District": 17
        },
        "Sunset District": {
            "Marina District": 21, "Embarcadero": 30, "Bayview": 22, "Union Square": 30, "Chinatown": 30,
            "Golden Gate Park": 11, "Financial District": 30, "Haight-Ashbury": 15, "Mission District": 25
        },
        "Golden Gate Park": {
            "Marina District": 16, "Embarcadero": 25, "Bayview": 23, "Union Square": 22, "Chinatown": 23,
            "Sunset District": 10, "Financial District": 26, "Haight-Ashbury": 7, "Mission District": 17
        },
        "Financial District": {
            "Marina District": 15, "Embarcadero": 4, "Bayview": 19, "Union Square": 9, "Chinatown": 5,
            "Sunset District": 30, "Golden Gate Park": 23, "Haight-Ashbury": 19, "Mission District": 17
        },
        "Haight-Ashbury": {
            "Marina District": 17, "Embarcadero": 20, "Bayview": 18, "Union Square": 19, "Chinatown": 19,
            "Sunset District": 15, "Golden Gate Park": 7, "Financial District": 21, "Mission District": 11
        },
        "Mission District": {
            "Marina District": 19, "Embarcadero": 19, "Bayview": 14, "Union Square": 15, "Chinatown": 16,
            "Sunset District": 24, "Golden Gate Park": 17, "Financial District": 15, "Haight-Ashbury": 12
        }
    }
    
    # Friend data: index, name, location, duration, available start (absolute), available end (absolute)
    friends = [
        (0, "Joshua", "Embarcadero", 105, 9*60+45, 18*60),      # 9:45 AM to 6:00 PM
        (1, "Jeffrey", "Bayview", 75, 9*60+45, 20*60+15),       # 9:45 AM to 8:15 PM
        (2, "Charles", "Union Square", 120, 10*60+45, 20*60+15), # 10:45 AM to 8:15 PM
        (3, "Joseph", "Chinatown", 60, 7*60, 15*60+30),         # 7:00 AM to 3:30 PM
        (4, "Matthew", "Golden Gate Park", 45, 11*60, 19*60+30), # 11:00 AM to 7:30 PM
        (5, "Carol", "Financial District", 15, 10*60+45, 11*60+15), # 10:45 AM to 11:15 AM
        (6, "Paul", "Haight-Ashbury", 15, 19*60+15, 20*60+30),  # 7:15 PM to 8:30 PM
        (7, "Rebecca", "Mission District", 45, 17*60, 21*60+45) # 5:00 PM to 9:45 PM
    ]
    
    # Base time: 9:00 AM in minutes from midnight = 540
    base_time = 540
    
    # For each friend, compute min_start (relative to base_time) and available_end_rel
    friend_min_start = []
    friend_available_end_rel = []
    friend_locations = []
    friend_durations = []
    friend_names = []
    for idx, name, loc, dur, start_abs, end_abs in friends:
        start_rel = start_abs - base_time
        travel_time = travel_dict["Marina District"][loc]
        min_start = max(start_rel, travel_time) if start_rel > 0 else travel_time
        friend_min_start.append(min_start)
        friend_available_end_rel.append(end_abs - base_time)
        friend_locations.append(loc)
        friend_durations.append(dur)
        friend_names.append(name)
    
    # Z3 variables
    meet = [Bool(f"meet_{i}") for i in range(8)]
    start = [Int(f"start_{i}") for i in range(8)]
    
    # Meeting0: start at Marina District at time 0 (relative to base_time)
    start0 = 0
    dur0 = 0
    loc0 = "Marina District"
    
    # Optimize context
    opt = Optimize()
    
    # Constraints for each friend
    for i in range(8):
        # If meeting the friend, enforce time window and duration constraints
        opt.add(Implies(meet[i], start[i] >= friend_min_start[i]))
        opt.add(Implies(meet[i], start[i] + friend_durations[i] <= friend_available_end_rel[i]))
        opt.add(Implies(meet[i], start[i] >= 0))  # Start time must be non-negative
        
        # Meeting0 constraint: travel from Marina to friend's location
        opt.add(Implies(meet[i], start[i] >= travel_dict[loc0][friend_locations[i]]))
    
    # Disjunctive constraints for every pair of friends (if both are met)
    for i in range(8):
        for j in range(i+1, 8):
            # Constraint: either i before j or j before i, with travel time
            cond = And(meet[i], meet[j])
            before = start[i] + friend_durations[i] + travel_dict[friend_locations[i]][friend_locations[j]] <= start[j]
            after = start[j] + friend_durations[j] + travel_dict[friend_locations[j]][friend_locations[i]] <= start[i]
            opt.add(Implies(cond, Or(before, after)))
    
    # Maximize the number of friends met
    opt.maximize(Sum([If(meet[i], 1, 0) for i in range(8)]))
    
    # Solve
    if opt.check() == sat:
        m = opt.model()
        scheduled_meetings = []
        for i in range(8):
            if m.eval(meet[i]):
                start_val = m.eval(start[i]).as_long()
                dur_val = friend_durations[i]
                start_abs_minutes = base_time + start_val
                end_abs_minutes = start_abs_minutes + dur_val
                start_hour = start_abs_minutes // 60
                start_minute = start_abs_minutes % 60
                end_hour = end_abs_minutes // 60
                end_minute = end_abs_minutes % 60
                start_time = f"{start_hour:02d}:{start_minute:02d}"
                end_time = f"{end_hour:02d}:{end_minute:02d}"
                scheduled_meetings.append((start_val, {
                    "action": "meet",
                    "person": friend_names[i],
                    "start_time": start_time,
                    "end_time": end_time
                }))
        # Sort by start time
        scheduled_meetings.sort(key=lambda x: x[0])
        itinerary = [entry for (_, entry) in scheduled_meetings]
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()