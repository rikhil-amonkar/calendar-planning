from z3 import *
import math

def main():
    # City names and their indices
    city_names = ['Mykonos', 'Naples', 'Istanbul', 'Venice', 'Dublin', 'Frankfurt', 'Brussels', 'Krakow']
    city_index = {name: idx for idx, name in enumerate(city_names)}
    
    # Transportation data
    transportation = {
        'Mykonos': {'Naples': ['Tuesday', 'Saturday'], 'Istanbul': ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'], 'Venice': ['Monday', 'Wednesday', 'Friday'], 'Krakow': ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday']},
        'Naples': {'Mykonos': ['Tuesday', 'Saturday'], 'Istanbul': ['Monday', 'Wednesday', 'Friday'], 'Venice': ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'], 'Brussels': ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday']},
        'Istanbul': {'Mykonos': ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'], 'Naples': ['Monday', 'Wednesday', 'Friday'], 'Venice': ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'], 'Dublin': ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'], 'Krakow': ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday']},
        'Venice': {'Mykonos': ['Monday', 'Wednesday', 'Friday'], 'Naples': ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'], 'Istanbul': ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'], 'Brussels': ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday']},
        'Dublin': {'Istanbul': ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'], 'Frankfurt': ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'], 'Krakow': ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday']},
        'Frankfurt': {'Dublin': ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'], 'Brussels': ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'], 'Krakow': ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday']},
        'Brussels': {'Naples': ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'], 'Venice': ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'], 'Frankfurt': ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'], 'Krakow': ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday']},
        'Krakow': {'Mykonos': ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'], 'Istanbul': ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'], 'Dublin': ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'], 'Frankfurt': ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday'], 'Brussels': ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday']}
    }
    
    # Precompute directed_valid_pairs: (a, b, [list of allowed day indices])
    day_names = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday']
    directed_valid_pairs = []
    for cityA, connections in transportation.items():
        for cityB, days in connections.items():
            a_idx = city_index[cityA]
            b_idx = city_index[cityB]
            day_indices = [day_names.index(day) for day in days]
            directed_valid_pairs.append((a_idx, b_idx, day_indices))
    
    # Total stays: 15 (8 non-travel, 7 travel)
    n_non_travel = 8
    total_stays = 15
    s = [Int(f's_{i}') for i in range(total_stays)]
    e = [Int(f'e_{i}') for i in range(total_stays)]
    non_travel_city = [Int(f'nc_{i}') for i in range(n_non_travel)]
    
    solver = Solver()
    
    # Constraint: non_travel_city distinct and fixed first and last
    solver.add(Distinct(non_travel_city))
    solver.add(non_travel_city[0] == city_index['Mykonos'])
    solver.add(non_travel_city[7] == city_index['Krakow'])
    
    # Constraints for start and end days
    solver.add(s[0] == 1)
    solver.add(e[14] == 21)
    
    # Continuity constraints
    for i in range(total_stays - 1):
        solver.add(e[i] + 1 == s[i+1])
    
    # Duration constraints
    for i in range(total_stays):
        if i % 2 == 0:  # non-travel stay
            solver.add(e[i] - s[i] + 1 >= 2)
        else:  # travel stay
            solver.add(e[i] == s[i])
    
    # Transportation constraints for travel stays
    for i in range(1, total_stays, 2):  # i = 1,3,...,13
        k = (i-1)//2
        a = non_travel_city[k]
        b = non_travel_city[k+1]
        travel_day = s[i]
        day_idx = (travel_day - 1) % 7  # day index (0-6)
        
        conds = []
        for (a0, b0, day_list) in directed_valid_pairs:
            for d0 in day_list:
                conds.append(And(a == a0, b == b0, day_idx == d0))
        solver.add(Or(conds))
    
    # Solve
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(total_stays):
            s_val = model.eval(s[i]).as_long()
            e_val = model.eval(e[i]).as_long()
            if i % 2 == 0:  # non-travel
                k = i // 2
                city_val = model.eval(non_travel_city[k]).as_long()
                place = city_names[city_val]
            else:  # travel
                k = (i-1) // 2
                a_val = model.eval(non_travel_city[k]).as_long()
                b_val = model.eval(non_travel_city[k+1]).as_long()
                place = f"{city_names[a_val]}/{city_names[b_val]}"
            
            if s_val == e_val:
                day_range = f"Day {s_val}"
            else:
                day_range = f"Day {s_val}-{e_val}"
            itinerary.append({'day_range': day_range, 'place': place})
        
        # Format the output
        print("{'itinerary': [")
        for i, stay in enumerate(itinerary):
            suffix = "," if i < len(itinerary)-1 else ""
            print(f"    {{'day_range': '{stay['day_range']}', 'place': '{stay['place']}'}}{suffix}")
        print("]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()