from z3 import *
import json

def main():
    # Define friends with their details: name, location, available_start (minutes from 9:00 AM), available_end, min_duration
    friends = [
        ('Joshua', 'Presidio', 0, 255, 105),  # Adjusted available_start to 0 (9:00 AM) since we start then
        ('David', 'Embarcadero', 105, 210, 30),
        ('Kimberly', 'Haight-Ashbury', 465, 750, 75),
        ('Lisa', 'Golden Gate Park', 510, 765, 45),
        ('Stephanie', 'Alamo Square', 390, 450, 30),
        ('Helen', 'Financial District', 510, 570, 45),
        ('Laura', 'Sunset District', 525, 735, 90),
        ('Elizabeth', 'Marina District', 600, 705, 105),  # Fixed meeting
        ('Timothy', 'North Beach', 645, 780, 90)
    ]
    
    # Locations including the starting point (The Castro) and all friend locations
    locations = [
        'The Castro', 'Marina District', 'Presidio', 'North Beach', 'Embarcadero',
        'Haight-Ashbury', 'Golden Gate Park', 'Alamo Square', 'Financial District', 'Sunset District'
    ]
    
    # Travel time data (from_loc, to_loc, time in minutes)
    travel_data = [
        ("The Castro", "Marina District", 21),
        ("The Castro", "Presidio", 20),
        ("The Castro", "North Beach", 20),
        ("The Castro", "Embarcadero", 22),
        ("The Castro", "Haight-Ashbury", 6),
        ("The Castro", "Golden Gate Park", 11),
        ("The Castro", "Alamo Square", 8),
        ("The Castro", "Financial District", 21),
        ("The Castro", "Sunset District", 17),
        ("Marina District", "The Castro", 22),
        ("Marina District", "Presidio", 10),
        ("Marina District", "North Beach", 11),
        ("Marina District", "Embarcadero", 14),
        ("Marina District", "Haight-Ashbury", 16),
        ("Marina District", "Golden Gate Park", 18),
        ("Marina District", "Alamo Square", 15),
        ("Marina District", "Financial District", 17),
        ("Marina District", "Sunset District", 19),
        ("Presidio", "The Castro", 21),
        ("Presidio", "Marina District", 11),
        ("Presidio", "North Beach", 18),
        ("Presidio", "Embarcadero", 20),
        ("Presidio", "Haight-Ashbury", 15),
        ("Presidio", "Golden Gate Park", 12),
        ("Presidio", "Alamo Square", 19),
        ("Presidio", "Financial District", 23),
        ("Presidio", "Sunset District", 15),
        ("North Beach", "The Castro", 23),
        ("North Beach", "Marina District", 9),
        ("North Beach", "Presidio", 17),
        ("North Beach", "Embarcadero", 6),
        ("North Beach", "Haight-Ashbury", 18),
        ("North Beach", "Golden Gate Park", 22),
        ("North Beach", "Alamo Square", 16),
        ("North Beach", "Financial District", 8),
        ("North Beach", "Sunset District", 27),
        ("Embarcadero", "The Castro", 25),
        ("Embarcadero", "Marina District", 12),
        ("Embarcadero", "Presidio", 20),
        ("Embarcadero", "North Beach", 5),
        ("Embarcadero", "Haight-Ashbury", 21),
        ("Embarcadero", "Golden Gate Park", 25),
        ("Embarcadero", "Alamo Square", 19),
        ("Embarcadero", "Financial District", 5),
        ("Embarcadero", "Sunset District", 30),
        ("Haight-Ashbury", "The Castro", 6),
        ("Haight-Ashbury", "Marina District", 17),
        ("Haight-Ashbury", "Presidio", 15),
        ("Haight-Ashbury", "North Beach", 19),
        ("Haight-Ashbury", "Embarcadero", 20),
        ("Haight-Ashbury", "Golden Gate Park", 7),
        ("Haight-Ashbury", "Alamo Square", 5),
        ("Haight-Ashbury", "Financial District", 21),
        ("Haight-Ashbury", "Sunset District", 15),
        ("Golden Gate Park", "The Castro", 13),
        ("Golden Gate Park", "Marina District", 16),
        ("Golden Gate Park", "Presidio", 11),
        ("Golden Gate Park", "North Beach", 23),
        ("Golden Gate Park", "Embarcadero", 25),
        ("Golden Gate Park", "Haight-Ashbury", 7),
        ("Golden Gate Park", "Alamo Square", 9),
        ("Golden Gate Park", "Financial District", 26),
        ("Golden Gate Park", "Sunset District", 10),
        ("Alamo Square", "The Castro", 8),
        ("Alamo Square", "Marina District", 15),
        ("Alamo Square", "Presidio", 17),
        ("Alamo Square", "North Beach", 15),
        ("Alamo Square", "Embarcadero", 16),
        ("Alamo Square", "Haight-Ashbury", 5),
        ("Alamo Square", "Golden Gate Park", 9),
        ("Alamo Square", "Financial District", 17),
        ("Alamo Square", "Sunset District", 16),
        ("Financial District", "The Castro", 20),
        ("Financial District", "Marina District", 15),
        ("Financial District", "Presidio", 22),
        ("Financial District", "North Beach", 7),
        ("Financial District", "Embarcadero", 4),
        ("Financial District", "Haight-Ashbury", 19),
        ("Financial District", "Golden Gate Park", 23),
        ("Financial District", "Alamo Square", 17),
        ("Financial District", "Sunset District", 30),
        ("Sunset District", "The Castro", 17),
        ("Sunset District", "Marina District", 21),
        ("Sunset District", "Presidio", 16),
        ("Sunset District", "North Beach", 28),
        ("Sunset District", "Embarcadero", 30),
        ("Sunset District", "Haight-Ashbury", 15),
        ("Sunset District", "Golden Gate Park", 11),
        ("Sunset District", "Alamo Square", 17),
        ("Sunset District", "Financial District", 30)
    ]
    
    # Build travel_time_dict: only include pairs within our locations
    travel_time_dict = {}
    our_locations_set = set(locations)
    for from_loc, to_loc, time in travel_data:
        if from_loc in our_locations_set and to_loc in our_locations_set:
            travel_time_dict[(from_loc, to_loc)] = time
    for loc in our_locations_set:
        travel_time_dict[(loc, loc)] = 0
    
    # Initialize Z3 solver and variables
    opt = Optimize()
    n = len(friends)
    
    # Create variables for each friend
    meet_vars = []      # Bool: whether we meet this friend
    start_vars = []     # Int: start time in minutes from 9:00 AM
    end_vars = []       # Int: end time in minutes from 9:00 AM
    friend_info = []    # Store friend details for reference
    
    for i, (name, loc, avail_start, avail_end, min_dur) in enumerate(friends):
        if name == 'Elizabeth':
            # Elizabeth is fixed: meet from 7:00 PM (600 minutes) to 8:45 PM (705 minutes)
            meet_var = True
            start_var = 600
            end_var = 705
        else:
            meet_var = Bool(f'meet_{name}')
            start_var = Int(f'start_{name}')
            end_var = Int(f'end_{name}')
        meet_vars.append(meet_var)
        start_vars.append(start_var)
        end_vars.append(end_var)
        friend_info.append({
            'name': name,
            'loc': loc,
            'avail_start': avail_start,
            'avail_end': avail_end,
            'min_dur': min_dur
        })
    
    # Add constraints for each friend (except Elizabeth, who is fixed)
    for i in range(n):
        name = friend_info[i]['name']
        if name == 'Elizabeth':
            continue
        loc = friend_info[i]['loc']
        avail_start = friend_info[i]['avail_start']
        avail_end = friend_info[i]['avail_end']
        min_dur = friend_info[i]['min_dur']
        
        # If meeting, constraints on start and end times
        opt.add(Implies(meet_vars[i], start_vars[i] >= avail_start))
        opt.add(Implies(meet_vars[i], end_vars[i] == start_vars[i] + min_dur))
        opt.add(Implies(meet_vars[i], end_vars[i] <= avail_end))
        # Travel time from The Castro to this location
        travel_from_start = travel_time_dict[('The Castro', loc)]
        opt.add(Implies(meet_vars[i], start_vars[i] >= travel_from_start))
    
    # Create pairwise 'before' variables for ordering
    before_vars = {}
    for i in range(n):
        for j in range(i+1, n):
            before_vars[(i, j)] = Bool(f'before_{i}_{j}')
    
    # Add ordering constraints for every pair of friends
    for i in range(n):
        for j in range(i+1, n):
            loc_i = friend_info[i]['loc']
            loc_j = friend_info[j]['loc']
            travel_ij = travel_time_dict[(loc_i, loc_j)]
            travel_ji = travel_time_dict[(loc_j, loc_i)]
            
            # If both meetings are scheduled, enforce ordering with travel time
            constraint = Implies(
                And(
                    meet_vars[i] if isinstance(meet_vars[i], bool) else meet_vars[i],
                    meet_vars[j] if isinstance(meet_vars[j], bool) else meet_vars[j]
                ),
                Or(
                    And(before_vars[(i, j)], start_vars[j] >= end_vars[i] + travel_ij),
                    And(Not(before_vars[(i, j)]), start_vars[i] >= end_vars[j] + travel_ji)
                )
            )
            opt.add(constraint)
    
    # Objective: maximize the number of meetings (Elizabeth is always included)
    total_meetings = 1  # Elizabeth
    for i in range(n):
        if friend_info[i]['name'] != 'Elizabeth':
            total_meetings += If(meet_vars[i], 1, 0)
    opt.maximize(total_meetings)
    
    # Solve the optimization problem
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for i in range(n):
            name = friend_info[i]['name']
            if name == 'Elizabeth':
                # Fixed meeting
                start_val = 600
                end_val = 705
                meet = True
            else:
                meet_val = model.eval(meet_vars[i])
                if is_true(meet_val):
                    start_val = model.eval(start_vars[i]).as_long()
                    end_val = model.eval(end_vars[i]).as_long()
                else:
                    continue
            
            # Convert minutes to time strings (from 9:00 AM base)
            base_hour = 9
            total_minutes_start = start_val
            hours_start = total_minutes_start // 60
            minutes_start = total_minutes_start % 60
            abs_hour_start = base_hour + hours_start
            # Adjust for 24-hour format
            start_str = f"{abs_hour_start:02d}:{minutes_start:02d}"
            
            total_minutes_end = end_val
            hours_end = total_minutes_end // 60
            minutes_end = total_minutes_end % 60
            abs_hour_end = base_hour + hours_end
            end_str = f"{abs_hour_end:02d}:{minutes_end:02d}"
            
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_str,
                "end_time": end_str
            })
        
        # Sort itinerary by start_time
        itinerary.sort(key=lambda x: (int(x['start_time'].split(':')[0]), int(x['start_time'].split(':')[1]))
        print('SOLUTION:')
        print(json.dumps({'itinerary': itinerary}))
    else:
        print('SOLUTION:')
        print(json.dumps({'itinerary': []}))

if __name__ == '__main__':
    main()