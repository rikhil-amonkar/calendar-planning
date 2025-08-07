from z3 import *

def main():
    # City mapping: index to name
    cities = ["Dublin", "Helsinki", "Riga", "Reykjavik", "Vienna", "Tallinn"]
    # Required days per city: [Dublin, Helsinki, Riga, Reykjavik, Vienna, Tallinn]
    required_days = [5, 3, 3, 2, 2, 5]
    
    # Allowed flights: set of tuples (from_index, to_index)
    allowed_flights = set([
        (0,1), (1,0),   # Dublin <-> Helsinki
        (0,2), (2,0),   # Dublin <-> Riga
        (0,3), (3,0),   # Dublin <-> Reykjavik
        (0,4), (4,0),   # Dublin <-> Vienna
        (0,5), (5,0),   # Dublin <-> Tallinn
        (1,2), (2,1),   # Helsinki <-> Riga
        (1,3), (3,1),   # Helsinki <-> Reykjavik
        (1,4), (4,1),   # Helsinki <-> Vienna
        (1,5), (5,1),   # Helsinki <-> Tallinn
        (2,4), (4,2),   # Riga <-> Vienna
        (3,4), (4,3),   # Reykjavik <-> Vienna
        (2,5)            # Riga -> Tallinn (unidirectional)
    ])
    
    # Create Z3 variables: L[0] to L[15]
    L = [Int('L_%d' % i) for i in range(16)]
    
    s = Solver()
    
    # Each L[i] must be between 0 and 5
    for i in range(16):
        s.add(And(L[i] >= 0, L[i] <= 5))
    
    # Flight constraints: if moving between cities, the flight must be allowed
    for t in range(1, 16):  # Days 1 to 15
        current_from = L[t-1]
        current_to = L[t]
        # If staying in the same city, no flight needed
        # If moving, ensure the flight (from, to) is in allowed_flights
        flight_constraint = Implies(
            current_from != current_to,
            Or([And(current_from == a, current_to == b) for (a, b) in allowed_flights])
        )
        s.add(flight_constraint)
    
    # Total days per city constraint
    for c in range(6):
        total = 0
        for t in range(1, 16):  # For each day from 1 to 15
            # If either the start (L[t-1]) or end (L[t]) of the day is city c, count the day
            total += If(Or(L[t-1] == c, L[t] == c), 1, 0)
        s.add(total == required_days[c])
    
    # Event constraints
    # Helsinki: must be present on at least one day between 3 and 5 (inclusive)
    helsinki_constraint = Or(
        Or(L[2] == 1, L[3] == 1),  # Day 3: uses L[2] and L[3]
        Or(L[3] == 1, L[4] == 1),  # Day 4: uses L[3] and L[4]
        Or(L[4] == 1, L[5] == 1)   # Day 5: uses L[4] and L[5]
    )
    s.add(helsinki_constraint)
    
    # Vienna: must be present on at least one day between 2 and 3 (inclusive)
    vienna_constraint = Or(
        Or(L[1] == 4, L[2] == 4),  # Day 2: uses L[1] and L[2]
        Or(L[2] == 4, L[3] == 4)   # Day 3: uses L[2] and L[3]
    )
    s.add(vienna_constraint)
    
    # Tallinn: must be present on at least one day between 7 and 11 (inclusive)
    tallinn_days = []
    for t in range(7, 12):  # Days 7 to 11
        tallinn_days.append(Or(L[t-1] == 5, L[t] == 5))
    s.add(Or(tallinn_days))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        itinerary_list = []
        for t in range(1, 16):  # Days 1 to 15
            # Get the city indices for the start (L[t-1]) and end (L[t]) of the day
            start_city = model[L[t-1]].as_long()
            end_city = model[L[t]].as_long()
            if start_city == end_city:
                cities_on_day = [cities[start_city]]
            else:
                cities_on_day = [cities[start_city], cities[end_city]]
            itinerary_list.append({"day": t, "cities": cities_on_day})
        
        # Output as a JSON-formatted dictionary
        result = {'itinerary': itinerary_list}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()