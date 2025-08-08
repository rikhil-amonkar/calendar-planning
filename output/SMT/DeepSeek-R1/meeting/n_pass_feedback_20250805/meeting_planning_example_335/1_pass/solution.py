from z3 import *
import json

def main():
    # Initialize variables
    meet_h, meet_k, meet_b, meet_a = Bools('meet_h meet_k meet_b meet_a')
    h_start = Int('h_start')
    k_start = Int('k_start')
    b_start = Int('b_start')
    a_start = Int('a_start')
    order_S, order_H, order_K, order_B, order_A = Ints('order_S order_H order_K order_B order_A')
    
    # Event setup
    events = ['S', 'H', 'K', 'B', 'A']
    held = {
        'S': True,
        'H': meet_h,
        'K': meet_k,
        'B': meet_b,
        'A': meet_a
    }
    time_var = {
        'S': 0,
        'H': h_start,
        'K': k_start,
        'B': b_start,
        'A': a_start
    }
    duration = {
        'S': 0,
        'H': 15,
        'K': 45,
        'B': 90,
        'A': 60
    }
    location = {
        'S': "Pacific Heights",
        'H': "North Beach",
        'K': "Mission District",
        'B': "Financial District",
        'A': "Alamo Square"
    }
    order_var = {
        'S': order_S,
        'H': order_H,
        'K': order_K,
        'B': order_B,
        'A': order_A
    }
    
    # Travel times dictionary
    travel_times = {
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Financial District"): 13,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Mission District"): 15,
        ("North Beach", "Pacific Heights"): 8,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Mission District"): 18,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Mission District"): 17,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Mission District"): 10,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "Financial District"): 17,
        ("Mission District", "Alamo Square"): 11
    }
    
    # Constraints
    constraints = []
    
    # Availability constraints
    constraints.append(Implies(meet_h, And(h_start >= 9, h_start + 15 <= 480)))       # Helen: 9:00AM to 5:00PM
    constraints.append(Implies(meet_k, And(k_start >= 105, k_start + 45 <= 345)))     # Kevin: 10:45AM to 2:45PM
    constraints.append(Implies(meet_b, And(b_start >= 600, b_start + 90 <= 765)))     # Betty: 7:00PM to 9:45PM
    constraints.append(Implies(meet_a, And(a_start >= 645, a_start + 60 <= 720)))     # Amanda: 7:45PM to 9:00PM
    
    # Order constraints for held events
    for e in events:
        if e != 'S':
            constraints.append(Implies(held[e], And(order_var[e] >= 0, order_var[e] <= 4)))
        else:
            constraints.append(And(order_var[e] >= 0, order_var[e] <= 4))
    
    # Distinct orders for held events
    for i in range(len(events)):
        for j in range(i + 1, len(events)):
            e1 = events[i]
            e2 = events[j]
            constraints.append(Implies(And(held[e1], held[e2]), order_var[e1] != order_var[e2]))
    
    # Travel time constraints for every pair of held events
    for i in range(len(events)):
        for j in range(len(events)):
            if i == j:
                continue
            e1 = events[i]
            e2 = events[j]
            loc1 = location[e1]
            loc2 = location[e2]
            constraints.append(
                Implies(And(held[e1], held[e2]),
                    If(order_var[e1] < order_var[e2],
                       time_var[e2] >= time_var[e1] + duration[e1] + travel_times[(loc1, loc2)],
                       time_var[e1] >= time_var[e2] + duration[e2] + travel_times[(loc2, loc1)]
                    )
                )
            )
    
    # Solve the problem
    opt = Optimize()
    for c in constraints:
        opt.add(c)
    
    # Maximize the number of meetings
    total_meetings = Sum([If(held[e], 1, 0) for e in ['H', 'K', 'B', 'A']])
    opt.maximize(total_meetings)
    
    itinerary = []
    if opt.check() == sat:
        m = opt.model()
        for e in ['H', 'K', 'B', 'A']:
            if is_true(m.evaluate(held[e])):
                start_minutes = m.evaluate(time_var[e]).as_long()
                hours = start_minutes // 60
                minutes = start_minutes % 60
                start_time = f"{hours:02d}:{minutes:02d}"
                
                end_minutes = start_minutes + duration[e]
                hours_end = end_minutes // 60
                minutes_end = end_minutes % 60
                end_time = f"{hours_end:02d}:{minutes_end:02d}"
                
                person_name = {
                    'H': 'Helen',
                    'K': 'Kevin',
                    'B': 'Betty',
                    'A': 'Amanda'
                }[e]
                
                itinerary.append({
                    "action": "meet",
                    "person": person_name,
                    "start_time": start_time,
                    "end_time": end_time
                })
        
        # Sort itinerary by start_time
        itinerary.sort(key=lambda x: x['start_time'])
    
    # Output the solution
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()