from z3 import *

def main():
    # Define travel times between locations
    travel_dict = {
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Russian Hill", "Bayview"): 23,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Bayview"): 31,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "Richmond District"): 20,
        ("Chinatown", "Fisherman's Wharf"): 8,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Bayview"): 22,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Bayview"): 22,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Chinatown"): 20,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Bayview"): 26,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Chinatown"): 12,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Bayview"): 23,
        ("Bayview", "Russian Hill"): 23,
        ("Bayview", "Presidio"): 31,
        ("Bayview", "Chinatown"): 18,
        ("Bayview", "Pacific Heights"): 23,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Golden Gate Park"): 22
    }
    
    # Mapping of node indices to locations and friends
    # node0: start (Russian Hill)
    # node1: Matthew (Presidio)
    # node2: Margaret (Chinatown)
    # node3: Nancy (Pacific Heights)
    # node4: Helen (Richmond District)
    # node5: Rebecca (Fisherman's Wharf)
    # node6: Kimberly (Golden Gate Park)
    # node7: Kenneth (Bayview)
    loc = {
        0: "Russian Hill",
        1: "Presidio",
        2: "Chinatown",
        3: "Pacific Heights",
        4: "Richmond District",
        5: "Fisherman's Wharf",
        6: "Golden Gate Park",
        7: "Bayview"
    }
    
    # Friend names for nodes 1 to 7
    friend_names = {
        1: "Matthew",
        2: "Margaret",
        3: "Nancy",
        4: "Helen",
        5: "Rebecca",
        6: "Kimberly",
        7: "Kenneth"
    }
    
    # Availability and duration in minutes from midnight
    # Index 0 unused for node0
    avail_start = [0, 11*60, 9*60+15, 14*60+15, 19*60+45, 21*60+15, 13*60, 14*60+30]
    avail_end = [0, 21*60, 18*60+45, 17*60, 22*60, 22*60+15, 16*60+30, 18*60]
    duration_list = [0, 90, 90, 15, 60, 60, 120, 60]
    
    s = Optimize()
    
    # Done variables for nodes 1-7 (index 0 to 6 in done list)
    done = [Bool(f'done_{i}') for i in range(1,8)]
    
    # Start and end times for nodes 1-7 (index 0 to 6 in start and end lists)
    start_times = [Int(f'start_{i}') for i in range(1,8)]
    end_times = [Int(f'end_{i}') for i in range(1,8)]
    
    # Next variables: next[i][j] for i in [0..7] and j in [1..7] with i != j
    next_var = {}
    for i in range(0,8):
        for j in range(1,8):
            if i != j:
                next_var[(i,j)] = Bool(f'next_{i}_{j}')
    
    # Position variables for nodes 0-7
    position = [Int(f'position_{i}') for i in range(0,8)]
    s.add(position[0] == 0)
    
    # Total done meetings
    total_done = Int('total_done')
    s.add(total_done == Sum([If(done[i], 1, 0) for i in range(7)]))
    s.maximize(total_done)
    
    # Constraint 1: Start node (0) has exactly one outgoing edge if total_done>=1, else 0
    s.add(Sum([If(next_var[(0,j)], 1, 0) for j in range(1,8)]) == If(total_done >= 1, 1, 0))
    
    # Constraint 2: For each meeting node j (1-7), incoming and outgoing edges
    for j in range(1,8):
        incoming = Sum([If(next_var[(i,j)], 1, 0) for i in range(0,8) if i != j])
        outgoing = Sum([If(next_var[(j,k)], 1, 0) for k in range(1,8) if k != j])
        s.add(If(done[j-1], 
                And(incoming == 1, outgoing <= 1, outgoing >= 0),
                And(incoming == 0, outgoing == 0)))
    
    # Constraint 3: Total edges equals total_done
    all_edges = [next_var[(i,j)] for i in range(0,8) for j in range(1,8) if i != j]
    s.add(Sum([If(edge, 1, 0) for edge in all_edges]) == total_done)
    
    # Constraint 4: Position constraints
    for i in range(0,8):
        for j in range(1,8):
            if i != j:
                s.add(If(next_var[(i,j)], position[j] == position[i] + 1, True))
    for j in range(1,8):
        s.add(If(done[j-1], And(position[j] >= 1, position[j] <= total_done), True))
    
    # Constraint 5: Meeting time constraints
    for j in range(1,8):
        idx = j-1
        s.add(If(done[idx],
                And(start_times[idx] >= avail_start[j],
                    end_times[idx] == start_times[idx] + duration_list[j],
                    end_times[idx] <= avail_end[j]),
                True))
        # Add bounds for start time to help solver
        s.add(If(done[idx], start_times[idx] >= 540, True))
        s.add(If(done[idx], start_times[idx] <= 1335, True))
    
    # Constraint 6: Travel time constraints
    for i in range(0,8):
        for j in range(1,8):
            if i == j:
                continue
            loc_i = loc[i]
            loc_j = loc[j]
            travel = travel_dict[(loc_i, loc_j)]
            if i == 0:
                s.add(If(next_var[(i,j)], start_times[j-1] >= 540 + travel, True))
            else:
                # For i>=1, end time of meeting i is end_times[i-1]
                s.add(If(next_var[(i,j)], start_times[j-1] >= end_times[i-1] + travel, True))
    
    # Constraint 7: If next[i][j] is set and i>=1, then done[i-1] and done[j-1] must be true
    for i in range(1,8):
        for j in range(1,8):
            if i != j:
                s.add(If(next_var[(i,j)], And(done[i-1], done[j-1]), True))
    
    # Solve the model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for j in range(1,8):
            idx = j-1
            if m.evaluate(done[idx]):
                start_val = m.evaluate(start_times[idx]).as_long()
                end_val = m.evaluate(end_times[idx]).as_long()
                start_h = start_val // 60
                start_m = start_val % 60
                end_h = end_val // 60
                end_m = end_val % 60
                start_str = f"{start_h:02d}:{start_m:02d}"
                end_str = f"{end_h:02d}:{end_m:02d}"
                friend = friend_names[j]
                itinerary.append({
                    "action": "meet",
                    "person": friend,
                    "start_time": start_str,
                    "end_time": end_str
                })
        # Sort itinerary by start_time
        itinerary_sorted = sorted(itinerary, key=lambda x: x['start_time'])
        result = {"itinerary": itinerary_sorted}
        print(f"SOLUTION: {result}")
    else:
        print("No solution found")
        result = {"itinerary": []}
        print(f"SOLUTION: {result}")

if __name__ == '__main__':
    main()