import json
from z3 import *

def main():
    # Define locations
    loc_names = [
        "Pacific Heights",
        "Golden Gate Park",
        "The Castro",
        "Bayview",
        "Marina District",
        "Union Square",
        "Sunset District",
        "Alamo Square",
        "Financial District",
        "Mission District"
    ]
    
    # Travel time data
    travel_data = [
        ("Pacific Heights", "Golden Gate Park", 15),
        ("Pacific Heights", "The Castro", 16),
        ("Pacific Heights", "Bayview", 22),
        ("Pacific Heights", "Marina District", 6),
        ("Pacific Heights", "Union Square", 12),
        ("Pacific Heights", "Sunset District", 21),
        ("Pacific Heights", "Alamo Square", 10),
        ("Pacific Heights", "Financial District", 13),
        ("Pacific Heights", "Mission District", 15),
        ("Golden Gate Park", "Pacific Heights", 16),
        ("Golden Gate Park", "The Castro", 13),
        ("Golden Gate Park", "Bayview", 23),
        ("Golden Gate Park", "Marina District", 16),
        ("Golden Gate Park", "Union Square", 22),
        ("Golden Gate Park", "Sunset District", 10),
        ("Golden Gate Park", "Alamo Square", 9),
        ("Golden Gate Park", "Financial District", 26),
        ("Golden Gate Park", "Mission District", 17),
        ("The Castro", "Pacific Heights", 16),
        ("The Castro", "Golden Gate Park", 11),
        ("The Castro", "Bayview", 19),
        ("The Castro", "Marina District", 21),
        ("The Castro", "Union Square", 19),
        ("The Castro", "Sunset District", 17),
        ("The Castro", "Alamo Square", 8),
        ("The Castro", "Financial District", 21),
        ("The Castro", "Mission District", 7),
        ("Bayview", "Pacific Heights", 23),
        ("Bayview", "Golden Gate Park", 22),
        ("Bayview", "The Castro", 19),
        ("Bayview", "Marina District", 27),
        ("Bayview", "Union Square", 18),
        ("Bayview", "Sunset District", 23),
        ("Bayview", "Alamo Square", 16),
        ("Bayview", "Financial District", 19),
        ("Bayview", "Mission District", 13),
        ("Marina District", "Pacific Heights", 7),
        ("Marina District", "Golden Gate Park", 18),
        ("Marina District", "The Castro", 22),
        ("Marina District", "Bayview", 27),
        ("Marina District", "Union Square", 16),
        ("Marina District", "Sunset District", 19),
        ("Marina District", "Alamo Square", 15),
        ("Marina District", "Financial District", 17),
        ("Marina District", "Mission District", 20),
        ("Union Square", "Pacific Heights", 15),
        ("Union Square", "Golden Gate Park", 22),
        ("Union Square", "The Castro", 17),
        ("Union Square", "Bayview", 15),
        ("Union Square", "Marina District", 18),
        ("Union Square", "Sunset District", 27),
        ("Union Square", "Alamo Square", 15),
        ("Union Square", "Financial District", 9),
        ("Union Square", "Mission District", 14),
        ("Sunset District", "Pacific Heights", 21),
        ("Sunset District", "Golden Gate Park", 11),
        ("Sunset District", "The Castro", 17),
        ("Sunset District", "Bayview", 22),
        ("Sunset District", "Marina District", 21),
        ("Sunset District", "Union Square", 30),
        ("Sunset District", "Alamo Square", 17),
        ("Sunset District", "Financial District", 30),
        ("Sunset District", "Mission District", 25),
        ("Alamo Square", "Pacific Heights", 10),
        ("Alamo Square", "Golden Gate Park", 9),
        ("Alamo Square", "The Castro", 8),
        ("Alamo Square", "Bayview", 16),
        ("Alamo Square", "Marina District", 15),
        ("Alamo Square", "Union Square", 14),
        ("Alamo Square", "Sunset District", 16),
        ("Alamo Square", "Financial District", 17),
        ("Alamo Square", "Mission District", 10),
        ("Financial District", "Pacific Heights", 13),
        ("Financial District", "Golden Gate Park", 23),
        ("Financial District", "The Castro", 20),
        ("Financial District", "Bayview", 19),
        ("Financial District", "Marina District", 15),
        ("Financial District", "Union Square", 9),
        ("Financial District", "Sunset District", 30),
        ("Financial District", "Alamo Square", 17),
        ("Financial District", "Mission District", 17),
        ("Mission District", "Pacific Heights", 16),
        ("Mission District", "Golden Gate Park", 17),
        ("Mission District", "The Castro", 7),
        ("Mission District", "Bayview", 14),
        ("Mission District", "Marina District", 19),
        ("Mission District", "Union Square", 15),
        ("Mission District", "Sunset District", 24),
        ("Mission District", "Alamo Square", 11),
        ("Mission District", "Financial District", 15)
    ]
    
    travel_dict = {}
    for item in travel_data:
        from_loc, to_loc, time = item
        travel_dict[(from_loc, to_loc)] = time

    n_locations = len(loc_names)
    all_travel = [[0] * n_locations for _ in range(n_locations)]
    for i in range(n_locations):
        for j in range(n_locations):
            if i == j:
                all_travel[i][j] = 0
            else:
                from_loc = loc_names[i]
                to_loc = loc_names[j]
                all_travel[i][j] = travel_dict.get((from_loc, to_loc), 10000)  # large number if not found

    n_meetings = 9
    T_matrix = [[0] * n_meetings for _ in range(n_locations)]
    for i in range(n_locations):
        for j in range(n_meetings):
            to_loc_index = j + 1  # because meeting j is at location index j+1
            T_matrix[i][j] = all_travel[i][to_loc_index]
    
    meetings = [
        {"name": "Helen", "location": "Golden Gate Park", "min_time": 45, "start_avail": 30, "end_avail": 195},
        {"name": "Steven", "location": "The Castro", "min_time": 105, "start_avail": 675, "end_avail": 780},
        {"name": "Deborah", "location": "Bayview", "min_time": 30, "start_avail": -30, "end_avail": 180},
        {"name": "Matthew", "location": "Marina District", "min_time": 45, "start_avail": 15, "end_avail": 315},
        {"name": "Joseph", "location": "Union Square", "min_time": 120, "start_avail": 315, "end_avail": 585},
        {"name": "Ronald", "location": "Sunset District", "min_time": 60, "start_avail": 420, "end_avail": 705},
        {"name": "Robert", "location": "Alamo Square", "min_time": 120, "start_avail": 570, "end_avail": 735},
        {"name": "Rebecca", "location": "Financial District", "min_time": 30, "start_avail": 345, "end_avail": 435},
        {"name": "Elizabeth", "location": "Mission District", "min_time": 120, "start_avail": 570, "end_avail": 720}
    ]
    available_start = [m["start_avail"] for m in meetings]
    available_end = [m["end_avail"] for m in meetings]
    duration = [m["min_time"] for m in meetings]
    
    s = Solver()
    meet = [Bool('meet_%d' % i) for i in range(n_meetings)]
    t = [Int('t_%d' % i) for i in range(n_meetings)]
    x = [[None] * (n_meetings + 2) for _ in range(n_meetings + 1)]  # rows: 0..n_meetings (start and meetings), columns: 1..n_meetings+1 (meetings and end)
    for k in range(0, n_meetings + 1):  # k: 0 to 9 (start and 9 meetings)
        for j in range(1, n_meetings + 2):  # j: 1 to 10 (meetings 1..9 and end=10)
            x[k][j] = Bool('x_%d_%d' % (k, j))
    
    # Start node (0) has exactly one outgoing edge
    s.add(Sum([If(x[0][j], 1, 0) for j in range(1, n_meetings + 2)]) == 1)
    # End node (n_meetings+1) has exactly one incoming edge
    s.add(Sum([If(x[i][n_meetings + 1], 1, 0) for i in range(0, n_meetings + 1)]) == 1)
    
    for i in range(n_meetings):
        i_node = i + 1  # meeting i is node i+1 in the graph
        s.add(If(meet[i],
                 And(
                     Sum([If(x[k][i_node], 1, 0) for k in range(0, n_meetings + 1) if k != i_node]) == 1,
                     Sum([If(x[i_node][j], 1, 0) for j in range(1, n_meetings + 2) if j != i_node]) == 1
                 ),
                 And(
                     Sum([If(x[k][i_node], 1, 0) for k in range(0, n_meetings + 1)]) == 0,
                     Sum([If(x[i_node][j], 1, 0) for j in range(1, n_meetings + 2)]) == 0
                 )))
        # Time window and duration constraints if meeting happens
        s.add(If(meet[i],
                 And(
                     t[i] >= available_start[i],
                     t[i] + duration[i] <= available_end[i]
                 ),
                 True))
        # For Steven (index1), if met, fix start time to 675
        if i == 1:  # Steven is index1
            s.add(If(meet[i], t[i] == 675, True))
        # Precedence constraints: for each possible predecessor k
        for k in range(0, n_meetings + 1):  # k: node index (0=start, 1..9=meetings)
            if k == i_node:
                continue
            if k == 0:
                travel_time = T_matrix[0][i]  # from start (loc0) to meeting i (loc i+1)
                s.add(If(And(meet[i], x[k][i_node]),
                         t[i] >= travel_time,
                         True))
            else:
                # k is a meeting node: k from 1 to 9 -> meeting index = k-1
                travel_time = T_matrix[k][i]  # from node k (loc k) to meeting i (loc i+1)
                s.add(If(And(meet[i], x[k][i_node]),
                         t[i] >= t[k - 1] + duration[k - 1] + travel_time,
                         True))
    
    # Maximize the number of meetings
    opt = Optimize()
    opt.add(s.assertions())
    opt.maximize(Sum([If(meet_i, 1, 0) for meet_i in meet]))
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for i in range(n_meetings):
            if model.evaluate(meet[i]):
                start_val = model.evaluate(t[i])
                if isinstance(start_val, IntNumRef):
                    start_min = start_val.as_long()
                    hours = 9 + start_min // 60
                    minutes = start_min % 60
                    start_time = f"{hours:02d}:{minutes:02d}"
                    end_min = start_min + duration[i]
                    hours_end = 9 + end_min // 60
                    minutes_end = end_min % 60
                    end_time = f"{hours_end:02d}:{minutes_end:02d}"
                    itinerary.append({
                        "action": "meet",
                        "person": meetings[i]["name"],
                        "start_time": start_time,
                        "end_time": end_time
                    })
        itinerary_sorted = sorted(itinerary, key=lambda x: x['start_time'])
        result = {"itinerary": itinerary_sorted}
        print("SOLUTION:")
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()