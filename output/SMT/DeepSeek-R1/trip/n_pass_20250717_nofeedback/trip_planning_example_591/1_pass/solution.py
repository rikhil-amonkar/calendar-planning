from z3 import *
import json

def main():
    cities = ['Stuttgart', 'Bucharest', 'Geneva', 'Valencia', 'Munich']
    dur = [2, 2, 4, 6, 7]  # durations in the same order as cities
    idx_to_city = {0: 'Stuttgart', 1: 'Bucharest', 2: 'Geneva', 3: 'Valencia', 4: 'Munich'}
    
    allowed_edges = set()
    edges = [(2, 4), (4, 3), (1, 3), (4, 1), (3, 0), (2, 3)]
    for u, v in edges:
        allowed_edges.add((u, v))
        allowed_edges.add((v, u))
    
    s = [Int(f's_{i}') for i in range(5)]
    city_at_pos = [Int(f'city_at_pos_{i}') for i in range(5)]
    start_pos = [Int(f'start_pos_{i}') for i in range(5)]
    
    solver = Solver()
    
    # city_at_pos must be a permutation of [0,1,2,3,4]
    solver.add(Distinct(city_at_pos))
    for i in range(5):
        solver.add(city_at_pos[i] >= 0, city_at_pos[i] < 5)
    
    # First city starts at day 1
    solver.add(start_pos[0] == 1)
    
    # Consecutive cities: next start = current start + current duration - 1
    for i in range(4):
        solver.add(start_pos[i+1] == start_pos[i] + dur[city_at_pos[i]] - 1)
    
    # Last city ends at day 17
    solver.add(start_pos[4] + dur[city_at_pos[4]] - 1 == 17)
    
    # Each city's start day is the start_pos at its position
    for j in range(5):
        solver.add(Or([And(city_at_pos[i] == j, s[j] == start_pos[i]) for i in range(5)]))
    
    # Direct flight constraints
    for i in range(4):
        conds = []
        for (u, v) in allowed_edges:
            conds.append(And(city_at_pos[i] == u, city_at_pos[i+1] == v))
        solver.add(Or(conds))
    
    # Additional constraints for Geneva and Munich
    solver.add(s[2] <= 4)  # Geneva starts by day 4
    solver.add(s[4] <= 10)  # Munich starts by day 10
    
    if solver.check() == sat:
        model = solver.model()
        s_vals = {}
        for i in range(5):
            s_vals[i] = model.evaluate(s[i]).as_long()
        
        e_vals = {}
        for i in range(5):
            e_vals[i] = s_vals[i] + dur[i] - 1
        
        itinerary_list = []
        for day in range(1, 18):
            cities_today = []
            for i in range(5):
                if s_vals[i] <= day <= e_vals[i]:
                    cities_today.append(idx_to_city[i])
            cities_today.sort()
            place_str = ", ".join(cities_today)
            itinerary_list.append({"day": day, "place": place_str})
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()