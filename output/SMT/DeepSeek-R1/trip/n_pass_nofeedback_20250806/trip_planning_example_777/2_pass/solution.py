import json
from z3 import Solver, Int, Or, And, Implies, If, sat

def main():
    cities = ["Dublin", "Helsinki", "Riga", "Reykjavik", "Vienna", "Tallinn"]
    required_days = [5, 3, 3, 2, 2, 5]  # Corresponding to cities order
    
    allowed_flights = [
        (0, 1), (1, 0),  # Dublin <-> Helsinki
        (0, 2), (2, 0),  # Dublin <-> Riga
        (0, 3), (3, 0),  # Dublin <-> Reykjavik
        (0, 4), (4, 0),  # Dublin <-> Vienna
        (0, 5), (5, 0),  # Dublin <-> Tallinn
        (1, 2), (2, 1),  # Helsinki <-> Riga
        (1, 3), (3, 1),  # Helsinki <-> Reykjavik
        (1, 4), (4, 1),  # Helsinki <-> Vienna
        (1, 5), (5, 1),  # Helsinki <-> Tallinn
        (2, 4), (4, 2),  # Riga <-> Vienna
        (3, 4), (4, 3),  # Reykjavik <-> Vienna
        (2, 5)            # Riga -> Tallinn (unidirectional)
    ]
    
    s = Solver()
    L = [Int(f'L_{i}') for i in range(16)]
    
    # Domain constraints: each L[i] must be an integer between 0 and 5
    for i in range(16):
        s.add(L[i] >= 0, L[i] <= 5)
    
    # Flight constraints
    for t in range(1, 16):
        current_from = L[t-1]
        current_to = L[t]
        flight_options = []
        for flight in allowed_flights:
            a, b = flight
            flight_options.append(And(current_from == a, current_to == b))
        s.add(Implies(current_from != current_to, Or(flight_options)))
    
    # Total days per city
    for c_idx in range(6):
        total_days = 0
        for day in range(1, 16):
            total_days += If(Or(L[day-1] == c_idx, L[day] == c_idx), 1, 0)
        s.add(total_days == required_days[c_idx])
    
    # Event constraints
    # Helsinki: must be present on at least one day between 3 and 5 (inclusive)
    s.add(Or(
        Or(L[2] == 1, L[3] == 1),  # Day 3
        Or(L[3] == 1, L[4] == 1),  # Day 4
        Or(L[4] == 1, L[5] == 1)   # Day 5
    ))
    
    # Vienna: must be present on at least one day between 2 and 3 (inclusive)
    s.add(Or(
        Or(L[1] == 4, L[2] == 4),  # Day 2
        Or(L[2] == 4, L[3] == 4)   # Day 3
    ))
    
    # Tallinn: must be present on at least one day between 7 and 11 (inclusive)
    tallinn_days = []
    for day in range(7, 12):
        tallinn_days.append(Or(L[day-1] == 5, L[day] == 5))
    s.add(Or(tallinn_days))
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, 16):
            start_city = model[L[day-1]].as_long()
            end_city = model[L[day]].as_long()
            if start_city == end_city:
                cities_list = [cities[start_city]]
            else:
                cities_list = [cities[start_city], cities[end_city]]
            itinerary.append({"day": day, "cities": cities_list})
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()