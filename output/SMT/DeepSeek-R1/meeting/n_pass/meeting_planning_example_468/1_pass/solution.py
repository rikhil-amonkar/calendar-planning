from z3 import *

def main():
    friends = ['R', 'A', 'J', 'S', 'M']
    name_map = {
        'R': 'Rebecca',
        'A': 'Amanda',
        'J': 'James',
        'S': 'Sarah',
        'M': 'Melissa'
    }
    
    travel_time = {
        'C': {'B': 19, 'P': 16, 'A': 8, 'F': 24, 'G': 11},
        'B': {'C': 20, 'P': 23, 'A': 16, 'F': 25, 'G': 22},
        'P': {'C': 16, 'B': 22, 'A': 10, 'F': 13, 'G': 15},
        'A': {'C': 8, 'B': 16, 'P': 10, 'F': 19, 'G': 9},
        'F': {'C': 26, 'B': 26, 'P': 12, 'A': 20, 'G': 25},
        'G': {'C': 13, 'B': 23, 'P': 16, 'A': 10, 'F': 24}
    }
    
    loc_map = {
        'R': 'B',
        'A': 'P',
        'J': 'A',
        'S': 'F',
        'M': 'G'
    }
    
    safe_bound = {
        'R': travel_time['C']['B'],
        'A': travel_time['C']['P'],
        'J': travel_time['C']['A'],
        'S': travel_time['C']['F'],
        'M': travel_time['C']['G']
    }
    
    window_upper = {
        'R': 225,
        'A': 765,
        'J': 735,
        'S': 750,
        'M': 585
    }
    
    window_lower = {
        'J': 45,
        'A': 570
    }
    
    s = Optimize()
    
    meet = {f: Bool(f"meet_{f}") for f in friends}
    start = {f: Int(f"start_{f}") for f in friends}
    
    for f in friends:
        s.add(Implies(meet[f], start[f] >= safe_bound[f]))
        s.add(Implies(meet[f], start[f] + 90 <= window_upper[f]))
        if f in window_lower:
            s.add(Implies(meet[f], start[f] >= window_lower[f]))
    
    for i in friends:
        for j in friends:
            if i == j:
                continue
            i_loc = loc_map[i]
            j_loc = loc_map[j]
            travel_ij = travel_time[i_loc][j_loc]
            travel_ji = travel_time[j_loc][i_loc]
            disj = Or(
                start[i] + 90 + travel_ij <= start[j],
                start[j] + 90 + travel_ji <= start[i]
            )
            s.add(Implies(And(meet[i], meet[j]), disj))
    
    total_meetings = Sum([If(meet[f], 1, 0) for f in friends])
    s.maximize(total_meetings)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for f in friends:
            if is_true(m.eval(meet[f])):
                start_min = m.eval(start[f]).as_long()
                total_min = start_min
                hours = total_min // 60
                minutes = total_min % 60
                start_time_str = f"{9 + hours:02d}:{minutes:02d}"
                end_min = start_min + 90
                end_hours = 9 + end_min // 60
                end_minutes = end_min % 60
                end_time_str = f"{end_hours:02d}:{end_minutes:02d}"
                itinerary.append((start_min, {
                    "action": "meet",
                    "person": name_map[f],
                    "start_time": start_time_str,
                    "end_time": end_time_str
                }))
        itinerary.sort(key=lambda x: x[0])
        itinerary_dict = {"itinerary": [item[1] for item in itinerary]}
        print(f"SOLUTION: {itinerary_dict}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()