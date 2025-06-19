from z3 import *

def main():
    cities = ["Santorini", "Valencia", "Madrid", "Seville", "Bucharest", "Vienna", "Riga", "Tallinn", "Krakow", "Frankfurt"]
    index = { city: i for i, city in enumerate(cities) }
    duration_arr = [3, 4, 2, 2, 3, 4, 4, 5, 5, 4]
    
    fixed = {
        "Vienna": (3, 6),
        "Madrid": (6, 7),
        "Krakow": (11, 15),
        "Riga": (20, 23),
        "Tallinn": (23, 27)
    }
    fixed_indices = { index[city]: (s, e) for city, (s, e) in fixed.items() }
    
    edges_initial = [
        (5, 4), (0, 2), (3, 1), (5, 3), (2, 1), (4, 6), (1, 4), (0, 4), (5, 1), (5, 2),
        (1, 8), (1, 9), (8, 9), (6, 7), (5, 8), (5, 9), (2, 3), (0, 5), (5, 6), (9, 7),
        (9, 4), (2, 9), (9, 6), (2, 4)
    ]
    directed_flights_set = set()
    for (i, j) in edges_initial:
        directed_flights_set.add((i, j))
        directed_flights_set.add((j, i))
    
    start = [Int(f'start_{i}') for i in range(10)]
    end = [Int(f'end_{i}') for i in range(10)]
    s = [Int(f's_{i}') for i in range(10)]
    
    solver = Solver()
    
    for i in range(10):
        solver.add(end[i] == start[i] + duration_arr[i] - 1)
        solver.add(start[i] >= 1, end[i] <= 27)
        if i in fixed_indices:
            s_val, e_val = fixed_indices[i]
            solver.add(start[i] == s_val, end[i] == e_val)
    
    solver.add(Distinct(s))
    for i in range(10):
        solver.add(s[i] >= 0, s[i] < 10)
    
    solver.add(start[s[0]] == 1)
    solver.add(end[s[9]] == 27)
    
    for k in range(9):
        solver.add(end[s[k]] == start[s[k+1]])
    
    for k in range(9):
        conds = []
        for (i, j) in directed_flights_set:
            conds.append(And(s[k] == i, s[k+1] == j))
        solver.add(Or(conds))
    
    if solver.check() == sat:
        m = solver.model()
        seq = [m.evaluate(s[i]).as_long() for i in range(10)]
        start_vals = [m.evaluate(start[i]).as_long() for i in range(10)]
        end_vals = [m.evaluate(end[i]).as_long() for i in range(10)]
        
        print("Trip schedule:")
        for pos, city_idx in enumerate(seq):
            city_name = cities[city_idx]
            s_day = start_vals[city_idx]
            e_day = end_vals[city_idx]
            print(f"{city_name}: days {s_day} to {e_day}")
        
        print("\nTravel days:")
        for k in range(9):
            from_city = cities[seq[k]]
            to_city = cities[seq[k+1]]
            travel_day = end_vals[seq[k]]
            print(f"Day {travel_day}: {from_city} to {to_city}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()