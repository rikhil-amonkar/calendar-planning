from z3 import *
import json

def main():
    # Define city names and their integer mappings
    cities = ["Zurich", "Hamburg", "Helsinki", "Bucharest", "Split"]
    city_to_int = {name: idx for idx, name in enumerate(cities)}
    
    # Define the undirected flight edges
    undirected_edges = [
        ("Zurich", "Helsinki"),
        ("Hamburg", "Bucharest"),
        ("Helsinki", "Hamburg"),
        ("Zurich", "Hamburg"),
        ("Zurich", "Bucharest"),
        ("Zurich", "Split"),
        ("Helsinki", "Split"),
        ("Split", "Hamburg")
    ]
    
    # Convert to directed edges (both directions)
    directed_edges = []
    for u, v in undirected_edges:
        u_int = city_to_int[u]
        v_int = city_to_int[v]
        directed_edges.append((u_int, v_int))
        directed_edges.append((v_int, u_int))
    
    # Required days per city: [Zurich, Hamburg, Helsinki, Bucharest, Split]
    required_days = [3, 2, 2, 2, 7]
    
    # Create Z3 variables for each day (12 days)
    L = [Int(f"L_{i}") for i in range(12)]
    
    s = Solver()
    
    # Domain constraint: each L[i] must be between 0 and 4
    for i in range(12):
        s.add(L[i] >= 0, L[i] <= 4)
    
    # Flight constraints: for consecutive days, if city changes, must have a direct flight
    for i in range(1, 12):
        prev_city = L[i-1]
        curr_city = L[i]
        # If the city changes, ensure a direct flight exists
        flight_constraint = Or([And(prev_city == u, curr_city == v) for (u, v) in directed_edges])
        s.add(If(prev_city != curr_city, flight_constraint, True))
    
    # Wedding in Zurich between day 1 and 3 (days 1, 2, or 3)
    zurich_int = city_to_int["Zurich"]
    in_zurich1 = Or(L[0] == zurich_int)  # Day 1: must be in Zurich at end or departing (but day1 can't depart)
    in_zurich2 = Or(L[1] == zurich_int, And(L[0] == zurich_int, L[1] != zurich_int))  # Day 2: in Zurich at end or departing
    in_zurich3 = Or(L[2] == zurich_int, And(L[1] == zurich_int, L[2] != zurich_int))  # Day 3: in Zurich at end or departing
    s.add(Or(in_zurich1, in_zurich2, in_zurich3))
    
    # Conference in Split on day 4 and day 10
    split_int = city_to_int["Split"]
    in_split4 = Or(L[3] == split_int, And(L[2] == split_int, L[3] != split_int))  # Day 4
    in_split10 = Or(L[9] == split_int, And(L[8] == split_int, L[9] != split_int))  # Day 10
    s.add(in_split4, in_split10)
    
    # Total days constraint for each city
    for c in range(5):
        count_end = Sum([If(L[i] == c, 1, 0) for i in range(12)])
        count_depart = Sum([If(And(L[i-1] == c, L[i] != c), 1, 0) for i in range(1, 12)])
        total_days = count_end + count_depart
        s.add(total_days == required_days[c])
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        itinerary_list = []
        for i in range(12):
            city_idx = m.evaluate(L[i]).as_long()
            city_name = cities[city_idx]
            itinerary_list.append({"day": i+1, "place": city_name})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()