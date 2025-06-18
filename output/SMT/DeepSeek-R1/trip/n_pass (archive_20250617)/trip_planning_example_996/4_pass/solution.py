from z3 import *

def main():
    cities = {
        "Mykonos": 0,
        "Nice": 1,
        "Zurich": 2,
        "Prague": 3,
        "Bucharest": 4,
        "Valencia": 5,
        "Riga": 6
    }
    idx_to_city = {v: k for k, v in cities.items()}
    
    required_days = {
        cities["Mykonos"]: 3,
        cities["Nice"]: 2,
        cities["Zurich"]: 5,
        cities["Prague"]: 3,
        cities["Bucharest"]: 5,
        cities["Valencia"]: 5,
        cities["Riga"]: 5
    }
    
    allowed_edges = set([
        (0, 1), (0, 2), (1, 2), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6),
        (3, 4), (3, 5), (3, 6), (4, 5), (4, 6)
    ])
    
    s_start = [Int(f's_start_{i}') for i in range(22)]
    s_end = [Int(f's_end_{i}') for i in range(22)]
    
    solver = Solver()
    
    for i in range(22):
        solver.add(s_start[i] >= 0, s_start[i] <= 6)
        solver.add(s_end[i] >= 0, s_end[i] <= 6)
    
    for i in range(21):
        solver.add(s_end[i] == s_start[i + 1])
    
    for city_idx, req in required_days.items():
        count = 0
        for i in range(22):
            count += If(Or(s_start[i] == city_idx, s_end[i] == city_idx), 1, 0)
        solver.add(count == req)
    
    for i in range(3):
        solver.add(s_start[i] == cities["Mykonos"])
        solver.add(s_end[i] == cities["Mykonos"])
    
    for i in range(6, 9):
        solver.add(s_start[i] == cities["Prague"])
        solver.add(s_end[i] == cities["Prague"])
    
    for i in range(22):
        same_city = s_start[i] == s_end[i]
        flight_conds = [same_city]
        for (a, b) in allowed_edges:
            flight_conds.append(And(s_start[i] == a, s_end[i] == b))
            flight_conds.append(And(s_start[i] == b, s_end[i] == a))
        solver.add(Or(flight_conds))
    
    travel_days = Sum([If(s_start[i] != s_end[i], 1, 0) for i in range(22)])
    solver.add(travel_days == 6)
    
    if solver.check() == sat:
        model = solver.model()
        schedule = []
        for i in range(22):
            start_val = model.eval(s_start[i]).as_long()
            end_val = model.eval(s_end[i]).as_long()
            start_city = idx_to_city[start_val]
            if start_val == end_val:
                schedule.append(f"Day {i + 1}: {start_city}")
            else:
                end_city = idx_to_city[end_val]
                schedule.append(f"Day {i + 1}: {start_city} and {end_city}")
        
        for day in schedule:
            print(day)
            
        counts = {city: 0 for city in cities}
        for i in range(22):
            start_val = model.eval(s_start[i]).as_long()
            end_val = model.eval(s_end[i]).as_long()
            city_start = idx_to_city[start_val]
            counts[city_start] += 1
            if start_val != end_val:
                city_end = idx_to_city[end_val]
                counts[city_end] += 1
        print("\nCounts per city:")
        for city, count in counts.items():
            print(f"{city}: {count} days")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()