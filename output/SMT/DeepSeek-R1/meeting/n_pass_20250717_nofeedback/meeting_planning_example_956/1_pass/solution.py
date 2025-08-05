from z3 import *
import json

def main():
    # Define friends with their details: (name, location, available_start (min), available_end (min), min_duration)
    friends = [
        ("William", "Alamo Square", 915, 1035, 60),
        ("Joshua", "Richmond District", 420, 1200, 15),
        ("Joseph", "Financial District", 675, 810, 15),
        ("David", "Union Square", 1005, 1155, 45),
        ("Brian", "Fisherman's Wharf", 825, 1245, 105),
        ("Karen", "Marina District", 690, 1110, 15),
        ("Anthony", "Haight-Ashbury", 435, 630, 30),
        ("Matthew", "Mission District", 1035, 1155, 120),
        ("Helen", "Pacific Heights", 480, 720, 75),
        ("Jeffrey", "Golden Gate Park", 1140, 1290, 60)
    ]
    
    # Define all locations including the starting point
    all_locations = [
        "The Castro", "Alamo Square", "Richmond District", "Financial District", 
        "Union Square", "Fisherman's Wharf", "Marina District", "Haight-Ashbury", 
        "Mission District", "Pacific Heights", "Golden Gate Park"
    ]
    
    # Build travel_times dictionary
    travel_times = {loc: {} for loc in all_locations}
    
    # Populate travel times
    travel_times["The Castro"]["Alamo Square"] = 8
    travel_times["The Castro"]["Richmond District"] = 16
    travel_times["The Castro"]["Financial District"] = 21
    travel_times["The Castro"]["Union Square"] = 19
    travel_times["The Castro"]["Fisherman's Wharf"] = 24
    travel_times["The Castro"]["Marina District"] = 21
    travel_times["The Castro"]["Haight-Ashbury"] = 6
    travel_times["The Castro"]["Mission District"] = 7
    travel_times["The Castro"]["Pacific Heights"] = 16
    travel_times["The Castro"]["Golden Gate Park"] = 11

    travel_times["Alamo Square"]["The Castro"] = 8
    travel_times["Alamo Square"]["Richmond District"] = 11
    travel_times["Alamo Square"]["Financial District"] = 17
    travel_times["Alamo Square"]["Union Square"] = 14
    travel_times["Alamo Square"]["Fisherman's Wharf"] = 19
    travel_times["Alamo Square"]["Marina District"] = 15
    travel_times["Alamo Square"]["Haight-Ashbury"] = 5
    travel_times["Alamo Square"]["Mission District"] = 10
    travel_times["Alamo Square"]["Pacific Heights"] = 10
    travel_times["Alamo Square"]["Golden Gate Park"] = 9

    travel_times["Richmond District"]["The Castro"] = 16
    travel_times["Richmond District"]["Alamo Square"] = 13
    travel_times["Richmond District"]["Financial District"] = 22
    travel_times["Richmond District"]["Union Square"] = 21
    travel_times["Richmond District"]["Fisherman's Wharf"] = 18
    travel_times["Richmond District"]["Marina District"] = 9
    travel_times["Richmond District"]["Haight-Ashbury"] = 10
    travel_times["Richmond District"]["Mission District"] = 20
    travel_times["Richmond District"]["Pacific Heights"] = 10
    travel_times["Richmond District"]["Golden Gate Park"] = 9

    travel_times["Financial District"]["The Castro"] = 20
    travel_times["Financial District"]["Alamo Square"] = 17
    travel_times["Financial District"]["Richmond District"] = 21
    travel_times["Financial District"]["Union Square"] = 9
    travel_times["Financial District"]["Fisherman's Wharf"] = 10
    travel_times["Financial District"]["Marina District"] = 15
    travel_times["Financial District"]["Haight-Ashbury"] = 19
    travel_times["Financial District"]["Mission District"] = 17
    travel_times["Financial District"]["Pacific Heights"] = 13
    travel_times["Financial District"]["Golden Gate Park"] = 23

    travel_times["Union Square"]["The Castro"] = 17
    travel_times["Union Square"]["Alamo Square"] = 15
    travel_times["Union Square"]["Richmond District"] = 20
    travel_times["Union Square"]["Financial District"] = 9
    travel_times["Union Square"]["Fisherman's Wharf"] = 15
    travel_times["Union Square"]["Marina District"] = 18
    travel_times["Union Square"]["Haight-Ashbury"] = 18
    travel_times["Union Square"]["Mission District"] = 14
    travel_times["Union Square"]["Pacific Heights"] = 15
    travel_times["Union Square"]["Golden Gate Park"] = 22

    travel_times["Fisherman's Wharf"]["The Castro"] = 27
    travel_times["Fisherman's Wharf"]["Alamo Square"] = 21
    travel_times["Fisherman's Wharf"]["Richmond District"] = 18
    travel_times["Fisherman's Wharf"]["Financial District"] = 11
    travel_times["Fisherman's Wharf"]["Union Square"] = 13
    travel_times["Fisherman's Wharf"]["Marina District"] = 9
    travel_times["Fisherman's Wharf"]["Haight-Ashbury"] = 22
    travel_times["Fisherman's Wharf"]["Mission District"] = 22
    travel_times["Fisherman's Wharf"]["Pacific Heights"] = 12
    travel_times["Fisherman's Wharf"]["Golden Gate Park"] = 25

    travel_times["Marina District"]["The Castro"] = 22
    travel_times["Marina District"]["Alamo Square"] = 15
    travel_times["Marina District"]["Richmond District"] = 11
    travel_times["Marina District"]["Financial District"] = 17
    travel_times["Marina District"]["Union Square"] = 16
    travel_times["Marina District"]["Fisherman's Wharf"] = 10
    travel_times["Marina District"]["Haight-Ashbury"] = 16
    travel_times["Marina District"]["Mission District"] = 20
    travel_times["Marina District"]["Pacific Heights"] = 7
    travel_times["Marina District"]["Golden Gate Park"] = 18

    travel_times["Haight-Ashbury"]["The Castro"] = 6
    travel_times["Haight-Ashbury"]["Alamo Square"] = 5
    travel_times["Haight-Ashbury"]["Richmond District"] = 10
    travel_times["Haight-Ashbury"]["Financial District"] = 21
    travel_times["Haight-Ashbury"]["Union Square"] = 19
    travel_times["Haight-Ashbury"]["Fisherman's Wharf"] = 23
    travel_times["Haight-Ashbury"]["Marina District"] = 17
    travel_times["Haight-Ashbury"]["Mission District"] = 11
    travel_times["Haight-Ashbury"]["Pacific Heights"] = 12
    travel_times["Haight-Ashbury"]["Golden Gate Park"] = 7

    travel_times["Mission District"]["The Castro"] = 7
    travel_times["Mission District"]["Alamo Square"] = 11
    travel_times["Mission District"]["Richmond District"] = 20
    travel_times["Mission District"]["Financial District"] = 15
    travel_times["Mission District"]["Union Square"] = 15
    travel_times["Mission District"]["Fisherman's Wharf"] = 22
    travel_times["Mission District"]["Marina District"] = 19
    travel_times["Mission District"]["Haight-Ashbury"] = 12
    travel_times["Mission District"]["Pacific Heights"] = 16
    travel_times["Mission District"]["Golden Gate Park"] = 17

    travel_times["Pacific Heights"]["The Castro"] = 16
    travel_times["Pacific Heights"]["Alamo Square"] = 10
    travel_times["Pacific Heights"]["Richmond District"] = 12
    travel_times["Pacific Heights"]["Financial District"] = 13
    travel_times["Pacific Heights"]["Union Square"] = 12
    travel_times["Pacific Heights"]["Fisherman's Wharf"] = 13
    travel_times["Pacific Heights"]["Marina District"] = 6
    travel_times["Pacific Heights"]["Haight-Ashbury"] = 11
    travel_times["Pacific Heights"]["Mission District"] = 15
    travel_times["Pacific Heights"]["Golden Gate Park"] = 15

    travel_times["Golden Gate Park"]["The Castro"] = 13
    travel_times["Golden Gate Park"]["Alamo Square"] = 9
    travel_times["Golden Gate Park"]["Richmond District"] = 7
    travel_times["Golden Gate Park"]["Financial District"] = 26
    travel_times["Golden Gate Park"]["Union Square"] = 22
    travel_times["Golden Gate Park"]["Fisherman's Wharf"] = 24
    travel_times["Golden Gate Park"]["Marina District"] = 16
    travel_times["Golden Gate Park"]["Haight-Ashbury"] = 7
    travel_times["Golden Gate Park"]["Mission District"] = 17
    travel_times["Golden Gate Park"]["Pacific Heights"] = 16

    # Create a list that includes the start meeting (at The Castro) and the friends
    all_meetings = [("Start", "The Castro", 540, 540, 0)] + friends
    n_total = len(all_meetings)
    
    # Initialize Z3 solver
    s = Solver()
    
    # Create variables: include[i] (boolean) and start[i] (integer) for each meeting
    include = [Bool(f'include_{i}') for i in range(n_total)]
    start = [Int(f'start_{i}') for i in range(n_total)]
    
    # Constraint: the start meeting is fixed and always included
    s.add(include[0] == True)
    s.add(start[0] == 540)
    
    # Constraints for each meeting (excluding the start meeting)
    for i in range(1, n_total):
        name, loc, avail_start, avail_end, dur = all_meetings[i]
        # If included, the meeting must start within its availability window and last at least the minimum duration
        s.add(Implies(include[i], And(start[i] >= avail_start, start[i] + dur <= avail_end)))
    
    # Constraints for every pair of meetings (including the start meeting)
    for i in range(n_total):
        for j in range(n_total):
            if i == j:
                continue
            loc_i = all_meetings[i][1]
            loc_j = all_meetings[j][1]
            dur_i = all_meetings[i][4]
            dur_j = all_meetings[j][4]
            travel_ij = travel_times[loc_i][loc_j]
            travel_ji = travel_times[loc_j][loc_i]
            
            # If both meetings are included, they must be scheduled with sufficient travel time
            s.add(Implies(And(include[i], include[j]),
                          Or(
                              start[i] + dur_i + travel_ij <= start[j],
                              start[j] + dur_j + travel_ji <= start[i]
                          )))
    
    # Objective: maximize the number of included meetings (excluding the start meeting)
    objective = Sum([If(include[i], 1, 0) for i in range(1, n_total)])
    s.maximize(objective)
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        # Collect included meetings (excluding the start meeting)
        itinerary_entries = []
        for i in range(1, n_total):
            if m.evaluate(include[i]):
                name = all_meetings[i][0]
                start_val = m.evaluate(start[i])
                start_min = start_val.as_long()
                dur = all_meetings[i][4]
                end_min = start_min + dur
                # Convert minutes to HH:MM
                start_hour = start_min // 60
                start_minute = start_min % 60
                end_hour = end_min // 60
                end_minute = end_min % 60
                start_time = f"{start_hour:02d}:{start_minute:02d}"
                end_time = f"{end_hour:02d}:{end_minute:02d}"
                itinerary_entries.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_time,
                    "end_time": end_time
                })
        # Sort meetings by start time
        itinerary_entries.sort(key=lambda x: (int(x['start_time'][:2]), int(x['start_time'][3:5]))
        result = {"itinerary": itinerary_entries}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()