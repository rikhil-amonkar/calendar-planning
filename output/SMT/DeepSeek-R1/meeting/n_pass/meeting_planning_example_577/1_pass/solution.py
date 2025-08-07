from z3 import *
import json

def main():
    # Friend indices: 0:Stephanie, 1:Kevin, 3:Steven, 4:Anthony, 5:Sandra (skipping Robert:2)
    friends = [0, 1, 3, 4, 5]
    names = {
        0: "Stephanie",
        1: "Kevin",
        3: "Steven",
        4: "Anthony",
        5: "Sandra"
    }
    durations = {
        0: 15,
        1: 75,
        3: 75,
        4: 15,
        5: 45
    }
    # Windows in minutes from 9:00 AM (0 minutes = 9:00 AM)
    windows_start_min = {
        0: 660,   # 8:00 PM (20:00) = 11*60 = 660
        1: 615,    # 7:15 PM (19:15) = 10*60 + 15 = 615
        3: 7,      # 9:07 AM (since travel time is 7 min, and Steven available from 8:30 AM, but we start at 9:00)
        4: 5,      # 9:05 AM
        5: 345     # 2:45 PM (14:45) = 5*60 + 45 = 345
    }
    windows_end_max = {
        0: 705,    # 8:45 PM (20:45) = 660 + 45 = 705
        1: 765,    # 9:45 PM (21:45) = 615 + 150 = 765? 7:15 PM to 9:45 PM is 2.5 hours = 150 min -> 615+150=765
        3: 480,    # 5:00 PM (17:00) = 8*60 = 480
        4: 645,    # 7:45 PM (19:45) = 10*60 + 45 = 645? 9:00 AM to 7:45 PM is 10h45m = 645 min
        5: 765     # 9:45 PM (21:45) = 765
    }
    travel_start = {
        0: 17,    # Haight-Ashbury to Russian Hill
        1: 23,    # Haight-Ashbury to Fisherman's Wharf
        3: 7,     # Haight-Ashbury to Golden Gate Park
        4: 5,     # Haight-Ashbury to Alamo Square
        5: 12     # Haight-Ashbury to Pacific Heights
    }
    # Location names for friends
    loc = {
        0: "Russian Hill",
        1: "Fisherman's Wharf",
        3: "Golden Gate Park",
        4: "Alamo Square",
        5: "Pacific Heights"
    }
    # Travel times between locations (directed)
    travel_dict = {
        "Russian Hill": {
            "Fisherman's Wharf": 7,
            "Golden Gate Park": 21,
            "Alamo Square": 15,
            "Pacific Heights": 7
        },
        "Fisherman's Wharf": {
            "Russian Hill": 7,
            "Golden Gate Park": 25,
            "Alamo Square": 20,
            "Pacific Heights": 12
        },
        "Golden Gate Park": {
            "Russian Hill": 19,
            "Fisherman's Wharf": 24,
            "Alamo Square": 10,
            "Pacific Heights": 16
        },
        "Alamo Square": {
            "Russian Hill": 13,
            "Fisherman's Wharf": 19,
            "Golden Gate Park": 9,
            "Pacific Heights": 10
        },
        "Pacific Heights": {
            "Russian Hill": 7,
            "Fisherman's Wharf": 13,
            "Golden Gate Park": 15,
            "Alamo Square": 10
        }
    }
    # Build travel_between matrix for friends
    travel_between = {}
    for i in friends:
        travel_between[i] = {}
        for j in friends:
            if i == j:
                travel_between[i][j] = 0
            else:
                travel_between[i][j] = travel_dict[loc[i]][loc[j]]
    
    # Set up Z3 solver
    n_slots = len(friends)
    solver = Solver()
    slots = [Int('slot_%d' % i) for i in range(n_slots)]
    starts = [Int('start_%d' % i) for i in range(n_slots)]
    ends = [Int('end_%d' % i) for i in range(n_slots)]
    
    # Constraints: slots are distinct and each in friends
    solver.add(Distinct(slots))
    for s in slots:
        solver.add(Or([s == f for f in friends]))
    
    # First slot constraints
    first_friend = slots[0]
    solver.add(starts[0] >= travel_start[first_friend])
    solver.add(starts[0] >= windows_start_min[first_friend])
    solver.add(ends[0] == starts[0] + durations[first_friend])
    solver.add(ends[0] <= windows_end_max[first_friend])
    
    # Subsequent slots
    for idx in range(1, n_slots):
        prev_friend = slots[idx-1]
        curr_friend = slots[idx]
        # Travel time expression using nested If
        travel_time = IntVal(0)
        for p in friends:
            for c in friends:
                if p != c:
                    travel_time = If(And(prev_friend == p, curr_friend == c), 
                                    IntVal(travel_between[p][c]), 
                                    travel_time)
        solver.add(starts[idx] >= ends[idx-1] + travel_time)
        solver.add(starts[idx] >= windows_start_min[curr_friend])
        solver.add(ends[idx] == starts[idx] + durations[curr_friend])
        solver.add(ends[idx] <= windows_end_max[curr_friend])
    
    # Check for a solution
    itinerary = []
    if solver.check() == sat:
        model = solver.model()
        slot_vals = [model.evaluate(s).as_long() for s in slots]
        start_vals = [model.evaluate(starts[i]).as_long() for i in range(n_slots)]
        end_vals = [model.evaluate(ends[i]).as_long() for i in range(n_slots)]
        
        for i in range(n_slots):
            friend_idx = slot_vals[i]
            name = names[friend_idx]
            start_min = start_vals[i]
            end_min = end_vals[i]
            # Convert minutes to time string (base: 9:00 AM)
            start_hour = 9 + start_min // 60
            start_minute = start_min % 60
            end_hour = 9 + end_min // 60
            end_minute = end_min % 60
            start_str = "%02d:%02d" % (start_hour, start_minute)
            end_str = "%02d:%02d" % (end_hour, end_minute)
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_str,
                "end_time": end_str
            })
    
    # Output the itinerary in JSON format
    print(json.dumps({"itinerary": itinerary}))

if __name__ == '__main__':
    main()