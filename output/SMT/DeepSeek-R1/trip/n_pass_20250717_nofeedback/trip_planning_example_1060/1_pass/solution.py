from z3 import *

def main():
    # Define cities
    cities = ["Reykjavik", "Munich", "Stuttgart", "Istanbul", "Vilnius", "Seville", "Geneva", "Valencia"]
    n_cities = len(cities)
    n_days = 25
    
    # Map city names to indices
    city_index = {name: idx for idx, name in enumerate(cities)}
    
    # Create Z3 variables for each day (0 to 25)
    city = [Int(f'city_{d}') for d in range(0, n_days+1)]
    
    s = Solver()
    
    # Allowed directed flights: (from, to)
    directed_flights = {
        (city_index["Reykjavik"], city_index["Stuttgart"]),  # Reykjavik -> Stuttgart
        (city_index["Vilnius"], city_index["Munich"])        # Vilnius -> Munich
    }
    bidirectional_edges = [
        (city_index["Geneva"], city_index["Istanbul"]), (city_index["Istanbul"], city_index["Geneva"]),
        (city_index["Reykjavik"], city_index["Munich"]), (city_index["Munich"], city_index["Reykjavik"]),
        (city_index["Stuttgart"], city_index["Valencia"]), (city_index["Valencia"], city_index["Stuttgart"]),
        (city_index["Stuttgart"], city_index["Istanbul"]), (city_index["Istanbul"], city_index["Stuttgart"]),
        (city_index["Munich"], city_index["Geneva"]), (city_index["Geneva"], city_index["Munich"]),
        (city_index["Istanbul"], city_index["Vilnius"]), (city_index["Vilnius"], city_index["Istanbul"]),
        (city_index["Valencia"], city_index["Seville"]), (city_index["Seville"], city_index["Valencia"]),
        (city_index["Valencia"], city_index["Istanbul"]), (city_index["Istanbul"], city_index["Valencia"]),
        (city_index["Seville"], city_index["Munich"]), (city_index["Munich"], city_index["Seville"]),
        (city_index["Munich"], city_index["Istanbul"]), (city_index["Istanbul"], city_index["Munich"]),
        (city_index["Valencia"], city_index["Geneva"]), (city_index["Geneva"], city_index["Valencia"]),
        (city_index["Valencia"], city_index["Munich"]), (city_index["Munich"], city_index["Valencia"])
    ]
    allowed_directed = directed_flights | set(bidirectional_edges)
    
    # Constraint: Start in Reykjavik (day0)
    s.add(city[0] == city_index["Reykjavik"])
    
    # Fixed stays for Reykjavik (days 1-4) and Stuttgart (day4)
    s.add(city[1] == city_index["Reykjavik"])
    s.add(city[2] == city_index["Reykjavik"])
    s.add(city[3] == city_index["Reykjavik"])
    s.add(city[4] == city_index["Stuttgart"])
    
    # Fixed stays for Munich (days 13-15) and Istanbul (days 19-22)
    s.add(city[13] == city_index["Munich"])
    s.add(city[14] == city_index["Munich"])
    s.add(city[15] == city_index["Munich"])
    s.add(city[19] == city_index["Istanbul"])
    s.add(city[20] == city_index["Istanbul"])
    s.add(city[21] == city_index["Istanbul"])
    s.add(city[22] == city_index["Istanbul"])
    
    # Flight constraints for days 1 to 25
    for d in range(1, n_days+1):
        prev = city[d-1]
        curr = city[d]
        # If city changes, ensure the flight is allowed
        s.add(If(prev != curr, Or([And(prev == i, curr == j) for (i, j) in allowed_directed]), True))
    
    # Function to check presence in a city on a day
    def present(c, d):
        # c: city index, d: day (1-25)
        return Or(city[d] == c, And(city[d-1] == c, city[d] != c))
    
    # Reykjavik constraints (days 1-4 present, else absent)
    reykjavik_idx = city_index["Reykjavik"]
    for d in range(1, 5):
        s.add(present(reykjavik_idx, d))
    for d in range(5, n_days+1):
        s.add(Not(present(reykjavik_idx, d)))
    
    # Munich constraints (only days 13-15 present)
    munich_idx = city_index["Munich"]
    for d in range(1, 13):
        s.add(Not(present(munich_idx, d)))
    for d in range(13, 16):
        s.add(present(munich_idx, d))
    for d in range(16, n_days+1):
        s.add(Not(present(munich_idx, d)))
    
    # Istanbul constraints (only days 19-22 present)
    istanbul_idx = city_index["Istanbul"]
    for d in range(1, 19):
        s.add(Not(present(istanbul_idx, d)))
    for d in range(19, 23):
        s.add(present(istanbul_idx, d))
    for d in range(23, n_days+1):
        s.add(Not(present(istanbul_idx, d)))
    
    # Stuttgart must be present on day 7
    stuttgart_idx = city_index["Stuttgart"]
    s.add(present(stuttgart_idx, 7))
    
    # Total days for other cities
    stuttgart_total = Sum([If(present(stuttgart_idx, d), 1, 0) for d in range(1, n_days+1)])
    s.add(stuttgart_total == 4)
    
    vilnius_idx = city_index["Vilnius"]
    vilnius_total = Sum([If(present(vilnius_idx, d), 1, 0) for d in range(1, n_days+1)])
    s.add(vilnius_total == 4)
    
    seville_idx = city_index["Seville"]
    seville_total = Sum([If(present(seville_idx, d), 1, 0) for d in range(1, n_days+1)])
    s.add(seville_total == 3)
    
    geneva_idx = city_index["Geneva"]
    geneva_total = Sum([If(present(geneva_idx, d), 1, 0) for d in range(1, n_days+1)])
    s.add(geneva_total == 5)
    
    valencia_idx = city_index["Valencia"]
    valencia_total = Sum([If(present(valencia_idx, d), 1, 0) for d in range(1, n_days+1)])
    s.add(valencia_total == 5)
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for d in range(1, n_days+1):
            c_idx = m.evaluate(city[d]).as_long()
            itinerary.append({"day": d, "place": cities[c_idx]})
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()