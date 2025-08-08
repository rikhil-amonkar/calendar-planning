import json
from z3 import *

def main():
    locations = [
        "Richmond District",   #0
        "The Castro",           #1
        "Nob Hill",             #2
        "Marina District",      #3
        "Pacific Heights",      #4
        "Haight-Ashbury",       #5
        "Mission District",     #6
        "Chinatown",            #7
        "Russian Hill",         #8
        "Alamo Square",         #9
        "Bayview"               #10
    ]
    
    travel_data = [
        ("Richmond District", "The Castro", 16),
        ("Richmond District", "Nob Hill", 17),
        ("Richmond District", "Marina District", 9),
        ("Richmond District", "Pacific Heights", 10),
        ("Richmond District", "Haight-Ashbury", 10),
        ("Richmond District", "Mission District", 20),
        ("Richmond District", "Chinatown", 20),
        ("Richmond District", "Russian Hill", 13),
        ("Richmond District", "Alamo Square", 13),
        ("Richmond District", "Bayview", 27),
        ("The Castro", "Richmond District", 16),
        ("The Castro", "Nob Hill", 16),
        ("The Castro", "Marina District", 21),
        ("The Castro", "Pacific Heights", 16),
        ("The Castro", "Haight-Ashbury", 6),
        ("The Castro", "Mission District", 7),
        ("The Castro", "Chinatown", 22),
        ("The Castro", "Russian Hill", 18),
        ("The Castro", "Alamo Square", 8),
        ("The Castro", "Bayview", 19),
        ("Nob Hill", "Richmond District", 14),
        ("Nob Hill", "The Castro", 17),
        ("Nob Hill", "Marina District", 11),
        ("Nob Hill", "Pacific Heights", 8),
        ("Nob Hill", "Haight-Ashbury", 13),
        ("Nob Hill", "Mission District", 13),
        ("Nob Hill", "Chinatown", 6),
        ("Nob Hill", "Russian Hill", 5),
        ("Nob Hill", "Alamo Square", 11),
        ("Nob Hill", "Bayview", 19),
        ("Marina District", "Richmond District", 11),
        ("Marina District", "The Castro", 22),
        ("Marina District", "Nob Hill", 12),
        ("Marina District", "Pacific Heights", 7),
        ("Marina District", "Haight-Ashbury", 16),
        ("Marina District", "Mission District", 20),
        ("Marina District", "Chinatown", 15),
        ("Marina District", "Russian Hill", 8),
        ("Marina District", "Alamo Square", 15),
        ("Marina District", "Bayview", 27),
        ("Pacific Heights", "Richmond District", 12),
        ("Pacific Heights", "The Castro", 16),
        ("Pacific Heights", "Nob Hill", 8),
        ("Pacific Heights", "Marina District", 6),
        ("Pacific Heights", "Haight-Ashbury", 11),
        ("Pacific Heights", "Mission District", 15),
        ("Pacific Heights", "Chinatown", 11),
        ("Pacific Heights", "Russian Hill", 7),
        ("Pacific Heights", "Alamo Square", 10),
        ("Pacific Heights", "Bayview", 22),
        ("Haight-Ashbury", "Richmond District", 10),
        ("Haight-Ashbury", "The Castro", 6),
        ("Haight-Ashbury", "Nob Hill", 15),
        ("Haight-Ashbury", "Marina District", 17),
        ("Haight-Ashbury", "Pacific Heights", 12),
        ("Haight-Ashbury", "Mission District", 11),
        ("Haight-Ashbury", "Chinatown", 19),
        ("Haight-Ashbury", "Russian Hill", 17),
        ("Haight-Ashbury", "Alamo Square", 5),
        ("Haight-Ashbury", "Bayview", 18),
        ("Mission District", "Richmond District", 20),
        ("Mission District", "The Castro", 7),
        ("Mission District", "Nob Hill", 12),
        ("Mission District", "Marina District", 19),
        ("Mission District", "Pacific Heights", 16),
        ("Mission District", "Haight-Ashbury", 12),
        ("Mission District", "Chinatown", 16),
        ("Mission District", "Russian Hill", 15),
        ("Mission District", "Alamo Square", 11),
        ("Mission District", "Bayview", 14),
        ("Chinatown", "Richmond District", 20),
        ("Chinatown", "The Castro", 22),
        ("Chinatown", "Nob Hill", 9),
        ("Chinatown", "Marina District", 12),
        ("Chinatown", "Pacific Heights", 10),
        ("Chinatown", "Haight-Ashbury", 19),
        ("Chinatown", "Mission District", 17),
        ("Chinatown", "Russian Hill", 7),
        ("Chinatown", "Alamo Square", 17),
        ("Chinatown", "Bayview", 20),
        ("Russian Hill", "Richmond District", 14),
        ("Russian Hill", "The Castro", 21),
        ("Russian Hill", "Nob Hill", 5),
        ("Russian Hill", "Marina District", 7),
        ("Russian Hill", "Pacific Heights", 7),
        ("Russian Hill", "Haight-Ashbury", 17),
        ("Russian Hill", "Mission District", 16),
        ("Russian Hill", "Chinatown", 9),
        ("Russian Hill", "Alamo Square", 15),
        ("Russian Hill", "Bayview", 23),
        ("Alamo Square", "Richmond District", 11),
        ("Alamo Square", "The Castro", 8),
        ("Alamo Square", "Nob Hill", 11),
        ("Alamo Square", "Marina District", 15),
        ("Alamo Square", "Pacific Heights", 10),
        ("Alamo Square", "Haight-Ashbury", 5),
        ("Alamo Square", "Mission District", 10),
        ("Alamo Square", "Chinatown", 15),
        ("Alamo Square", "Russian Hill", 13),
        ("Alamo Square", "Bayview", 16),
        ("Bayview", "Richmond District", 25),
        ("Bayview", "The Castro", 19),
        ("Bayview", "Nob Hill", 20),
        ("Bayview", "Marina District", 27),
        ("Bayview", "Pacific Heights", 23),
        ("Bayview", "Haight-Ashbury", 19),
        ("Bayview", "Mission District", 13),
        ("Bayview", "Chinatown", 19),
        ("Bayview", "Russian Hill", 23),
        ("Bayview", "Alamo Square", 16)
    ]
    
    travel_dict = {}
    for (A, B, time_val) in travel_data:
        travel_dict[(A, B)] = time_val
    
    durations = [0, 45, 105, 30, 15, 30, 75, 120, 30, 120, 90]
    # Extend durations to include end node (index 11) with duration 0
    durations_extended = durations + [0]
    available_starts = [0, 450, 375, 315, 135, 165, 240, 330, 300, 240, 555]
    available_ends = [0, 660, 615, 780, 645, 510, 405, 600, 660, 495, 675]
    
    friends = ["Matthew", "Rebecca", "Brian", "Emily", "Karen", "Stephanie", "James", "Steven", "Elizabeth", "William"]
    
    s = Optimize()
    n = 12  # 11 real nodes + 1 end node
    
    # Variables
    meet = [Bool(f"meet_{i}") for i in range(1, 11)]  # For nodes 1-10
    t = [Int(f"t_{i}") for i in range(n)]  # Start times for all nodes
    x = [[Bool(f"x_{i}_{j}") for j in range(n)] for i in range(n)]  # Edge variables
    
    # Path constraints
    for i in range(n):
        s.add(Not(x[i][i]))  # No self loops
    
    # Start node constraints
    s.add(Sum([x[0][j] for j in range(1, n)]) == 1)  # Exactly one outgoing edge
    s.add(Sum([x[i][0] for i in range(n)]) == 0)      # No incoming edges
    
    # End node constraints
    s.add(Sum([x[i][11] for i in range(0, 11)]) == 1)  # Exactly one incoming edge
    s.add(Sum([x[11][j] for j in range(n)]) == 0)       # No outgoing edges
    
    # Meeting node constraints
    for k in range(1, 11):
        # If meeting is held, exactly one incoming and one outgoing edge
        s.add(Implies(meet[k-1], Sum([x[i][k] for i in range(n) if i != k]) == 1))
        s.add(Implies(meet[k-1], Sum([x[k][j] for j in range(n) if j != k]) == 1))
        # If meeting not held, no incoming or outgoing edges
        s.add(Implies(Not(meet[k-1]), Sum([x[i][k] for i in range(n) if i != k]) == 0))
        s.add(Implies(Not(meet[k-1]), Sum([x[k][j] for j in range(n) if j != k]) == 0))
    
    # Time constraints
    s.add(t[0] == 0)  # Start at 9:00 AM (0 minutes)
    
    # Travel time constraints
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            if i == 11 or j == 11:  # End node handling
                travel_time = 0
            else:
                travel_time = travel_dict.get((locations[i], locations[j]), 0)
            
            # Use durations_extended to avoid index errors
            s.add(Implies(x[i][j], t[j] >= t[i] + durations_extended[i] + travel_time))
    
    # Time window constraints for meetings
    for k in range(1, 11):
        s.add(Implies(meet[k-1], t[k] >= available_starts[k]))
        s.add(Implies(meet[k-1], t[k] + durations[k] <= available_ends[k]))
        s.add(Implies(meet[k-1], t[k] >= 0))  # Prevent negative times
    
    # Objective: Maximize number of meetings
    obj = Sum([If(meet_i, 1, 0) for meet_i in meet])
    s.maximize(obj)
    
    # Solve and output
    if s.check() == sat:
        m = s.model()
        itinerary = []
        base_hour = 9  # 9:00 AM base
        
        for idx in range(1, 11):  # Check meetings 1-10
            if m.evaluate(meet[idx-1]):
                start_val = m[t[idx]].as_long()
                hours = start_val // 60
                minutes = start_val % 60
                abs_hour = base_hour + hours
                start_time = f"{abs_hour:02d}:{minutes:02d}"
                
                end_val = start_val + durations[idx]
                end_hours = end_val // 60
                end_minutes = end_val % 60
                abs_end_hour = base_hour + end_hours
                end_time = f"{abs_end_hour:02d}:{end_minutes:02d}"
                
                itinerary.append({
                    "action": "meet",
                    "person": friends[idx-1],
                    "start_time": start_time,
                    "end_time": end_time
                })
        
        # Sort by start time
        itinerary.sort(key=lambda x: x['start_time'])
        print('SOLUTION:')
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()