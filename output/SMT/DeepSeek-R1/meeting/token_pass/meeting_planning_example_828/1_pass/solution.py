from z3 import *
import json

def main():
    # Convert time to minutes from 9:00
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1]) if len(parts) > 1 else 0
        return (hour - 9) * 60 + minute

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        total_minutes = minutes
        hours = total_minutes // 60 + 9
        mins = total_minutes % 60
        return f"{hours}:{mins:02d}"

    # Define people data with converted times
    people = [
        {'name': 'Stephanie', 'location': 'Richmond District', 'start_avail': time_to_minutes("16:15"), 'end_avail': time_to_minutes("21:30"), 'min_dur': 75},
        {'name': 'William', 'location': 'Union Square', 'start_avail': time_to_minutes("10:45"), 'end_avail': time_to_minutes("17:30"), 'min_dur': 45},
        {'name': 'Elizabeth', 'location': 'Nob Hill', 'start_avail': time_to_minutes("12:15"), 'end_avail': time_to_minutes("15:00"), 'min_dur': 105},
        {'name': 'Joseph', 'location': 'Fisherman\'s Wharf', 'start_avail': time_to_minutes("12:45"), 'end_avail': time_to_minutes("14:00"), 'min_dur': 75},
        {'name': 'Anthony', 'location': 'Golden Gate Park', 'start_avail': time_to_minutes("13:00"), 'end_avail': time_to_minutes("20:30"), 'min_dur': 75},
        {'name': 'Barbara', 'location': 'Embarcadero', 'start_avail': time_to_minutes("19:15"), 'end_avail': time_to_minutes("20:30"), 'min_dur': 75},
        {'name': 'Carol', 'location': 'Financial District', 'start_avail': time_to_minutes("11:45"), 'end_avail': time_to_minutes("16:15"), 'min_dur': 60},
        {'name': 'Sandra', 'location': 'North Beach', 'start_avail': time_to_minutes("10:00"), 'end_avail': time_to_minutes("12:30"), 'min_dur': 15},
        {'name': 'Kenneth', 'location': 'Presidio', 'start_avail': time_to_minutes("21:15"), 'end_avail': time_to_minutes("22:15"), 'min_dur': 45}
    ]

    locations = [
        'Marina District',
        'Richmond District',
        'Union Square',
        'Nob Hill',
        'Fisherman\'s Wharf',
        'Golden Gate Park',
        'Embarcadero',
        'Financial District',
        'North Beach',
        'Presidio'
    ]
    
    loc_index = {loc: idx for idx, loc in enumerate(locations)}
    
    travel_matrix = [[0] * 10 for _ in range(10)]
    
    travel_data = [
        ("Marina District", "Richmond District", 11),
        ("Marina District", "Union Square", 16),
        ("Marina District", "Nob Hill", 12),
        ("Marina District", "Fisherman's Wharf", 10),
        ("Marina District", "Golden Gate Park", 18),
        ("Marina District", "Embarcadero", 14),
        ("Marina District", "Financial District", 17),
        ("Marina District", "North Beach", 11),
        ("Marina District", "Presidio", 10),
        ("Richmond District", "Marina District", 9),
        ("Richmond District", "Union Square", 21),
        ("Richmond District", "Nob Hill", 17),
        ("Richmond District", "Fisherman's Wharf", 18),
        ("Richmond District", "Golden Gate Park", 9),
        ("Richmond District", "Embarcadero", 19),
        ("Richmond District", "Financial District", 22),
        ("Richmond District", "North Beach", 17),
        ("Richmond District", "Presidio", 7),
        ("Union Square", "Marina District", 18),
        ("Union Square", "Richmond District", 20),
        ("Union Square", "Nob Hill", 9),
        ("Union Square", "Fisherman's Wharf", 15),
        ("Union Square", "Golden Gate Park", 22),
        ("Union Square", "Embarcadero", 11),
        ("Union Square", "Financial District", 9),
        ("Union Square", "North Beach", 10),
        ("Union Square", "Presidio", 24),
        ("Nob Hill", "Marina District", 11),
        ("Nob Hill", "Richmond District", 14),
        ("Nob Hill", "Union Square", 7),
        ("Nob Hill", "Fisherman's Wharf", 10),
        ("Nob Hill", "Golden Gate Park", 17),
        ("Nob Hill", "Embarcadero", 9),
        ("Nob Hill", "Financial District", 9),
        ("Nob Hill", "North Beach", 8),
        ("Nob Hill", "Presidio", 17),
        ("Fisherman's Wharf", "Marina District", 9),
        ("Fisherman's Wharf", "Richmond District", 18),
        ("Fisherman's Wharf", "Union Square", 13),
        ("Fisherman's Wharf", "Nob Hill", 11),
        ("Fisherman's Wharf", "Golden Gate Park", 25),
        ("Fisherman's Wharf", "Embarcadero", 8),
        ("Fisherman's Wharf", "Financial District", 11),
        ("Fisherman's Wharf", "North Beach", 6),
        ("Fisherman's Wharf", "Presidio", 17),
        ("Golden Gate Park", "Marina District", 16),
        ("Golden Gate Park", "Richmond District", 7),
        ("Golden Gate Park", "Union Square", 22),
        ("Golden Gate Park", "Nob Hill", 20),
        ("Golden Gate Park", "Fisherman's Wharf", 24),
        ("Golden Gate Park", "Embarcadero", 25),
        ("Golden Gate Park", "Financial District", 26),
        ("Golden Gate Park", "North Beach", 23),
        ("Golden Gate Park", "Presidio", 11),
        ("Embarcadero", "Marina District", 12),
        ("Embarcadero", "Richmond District", 21),
        ("Embarcadero", "Union Square", 10),
        ("Embarcadero", "Nob Hill", 10),
        ("Embarcadero", "Fisherman's Wharf", 6),
        ("Embarcadero", "Golden Gate Park", 25),
        ("Embarcadero", "Financial District", 5),
        ("Embarcadero", "North Beach", 5),
        ("Embarcadero", "Presidio", 20),
        ("Financial District", "Marina District", 15),
        ("Financial District", "Richmond District", 21),
        ("Financial District", "Union Square", 9),
        ("Financial District", "Nob Hill", 8),
        ("Financial District", "Fisherman's Wharf", 10),
        ("Financial District", "Golden Gate Park", 23),
        ("Financial District", "Embarcadero", 4),
        ("Financial District", "North Beach", 7),
        ("Financial District", "Presidio", 22),
        ("North Beach", "Marina District", 9),
        ("North Beach", "Richmond District", 18),
        ("North Beach", "Union Square", 7),
        ("North Beach", "Nob Hill", 7),
        ("North Beach", "Fisherman's Wharf", 5),
        ("North Beach", "Golden Gate Park", 22),
        ("North Beach", "Embarcadero", 6),
        ("North Beach", "Financial District", 8),
        ("North Beach", "Presidio", 17),
        ("Presidio", "Marina District", 11),
        ("Presidio", "Richmond District", 7),
        ("Presidio", "Union Square", 22),
        ("Presidio", "Nob Hill", 18),
        ("Presidio", "Fisherman's Wharf", 19),
        ("Presidio", "Golden Gate Park", 12),
        ("Presidio", "Embarcadero", 20),
        ("Presidio", "Financial District", 23),
        ("Presidio", "North Beach", 18)
    ]
    
    for from_loc, to_loc, time in travel_data:
        i = loc_index[from_loc]
        j = loc_index[to_loc]
        travel_matrix[i][j] = time

    n = 10  # 9 people + dummy start
    s = Optimize()
    
    held = [Bool(f'held_{i}') for i in range(n)]
    start_time = [Int(f'start_{i}') for i in range(n)]
    end_time = [Int(f'end_{i}') for i in range(n)]
    order = [Int(f'order_{i}') for i in range(n)]
    
    # Dummy meeting at Marina District at time 0
    s.add(held[0] == True)
    s.add(start_time[0] == 0)
    s.add(end_time[0] == 0)
    s.add(order[0] == 0)
    
    # Constraints for each person
    for i in range(1, n):
        p = people[i-1]
        s.add(Implies(held[i], start_time[i] >= p['start_avail']))
        s.add(Implies(held[i], end_time[i] <= p['end_avail']))
        s.add(Implies(held[i], end_time[i] - start_time[i] >= p['min_dur']))
    
    # Order constraints
    for i in range(n):
        s.add(Implies(held[i], And(order[i] >= 0, order[i] < n)))
        for j in range(i+1, n):
            s.add(Implies(And(held[i], held[j]), order[i] != order[j]))
    
    # Travel time constraints
    for i in range(n):
        for j in range(n):
            if i != j:
                cond = And(held[i], held[j], order[i] < order[j])
                travel_ij = travel_matrix[i][j]
                s.add(Implies(cond, start_time[j] >= end_time[i] + travel_ij))
    
    # Maximize number of meetings
    total_held = Sum([If(held[i], 1, 0) for i in range(1, n)])
    s.maximize(total_held)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        meeting_orders = []
        for i in range(1, n):
            if is_true(m.evaluate(held[i])):
                start_val = m.evaluate(start_time[i]).as_long()
                end_val = m.evaluate(end_time[i]).as_long()
                order_val = m.evaluate(order[i]).as_long()
                meeting_orders.append((order_val, i))
        
        meeting_orders.sort()
        for order_val, i in meeting_orders:
            p = people[i-1]
            start_val = m.evaluate(start_time[i]).as_long()
            end_val = m.evaluate(end_time[i]).as_long()
            start_str = minutes_to_time(start_val)
            end_str = minutes_to_time(end_val)
            itinerary.append({
                "action": "meet",
                "location": p['location'],
                "person": p['name'],
                "start_time": start_str,
                "end_time": end_str
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()