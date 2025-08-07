from z3 import *

def main():
    # City mapping
    cities = {
        'Manchester': 0,
        'Istanbul': 1,
        'Venice': 2,
        'Krakow': 3,
        'Lyon': 4
    }
    rev_cities = {v: k for k, v in cities.items()}
    
    # Direct flight edges
    edges = [
        (0, 2), (0, 1), (2, 1), (1, 3), (2, 4), (4, 1), (0, 3)
    ]
    allowed_pairs = []
    for (a, b) in edges:
        allowed_pairs.append((a, b))
        allowed_pairs.append((b, a))
    
    # Create solver and variables
    s = Solver()
    stay = [Int(f'stay_{i}') for i in range(21)]  # Days 1-21
    fly = [Bool(f'fly_{i}') for i in range(20)]   # Flights between days
    
    # City index constraints
    for i in range(21):
        s.add(stay[i] >= 0, stay[i] <= 4)
    
    # Flight constraints
    for i in range(20):
        s.add(If(
            fly[i],
            Or([And(stay[i] == a, stay[i+1] == b) for (a, b) in allowed_pairs]),
            stay[i] == stay[i+1]
        ))
    
    # Exactly 4 flights
    total_flights = Sum([If(fly[i], 1, 0) for i in range(20)])
    s.add(total_flights == 4)
    
    # Per-city day requirements (including flight days)
    for city, required in [(0, 3), (1, 7), (2, 7), (3, 6), (4, 2)]:
        base_days = Sum([If(stay[i] == city, 1, 0) for i in range(21)])
        flight_arrivals = Sum([If(And(fly[i], stay[i+1] == city), 1, 0) for i in range(20)])
        s.add(base_days + flight_arrivals == required)
    
    # Event constraints
    # Manchester wedding: at least one day in 1-3
    s.add(Or(
        stay[0] == 0,  # Day 1
        stay[1] == 0,  # Day 2
        stay[2] == 0   # Day 3
    ))
    
    # Venice workshop: must be present on day 3
    s.add(stay[2] == 2)  # Ensures Venice on day 3
    
    # Solve and output
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(1, 22):
            city_idx = m.eval(stay[day-1]).as_long()
            itinerary.append({"day": day, "place": rev_cities[city_idx]})
        print({'itinerary': itinerary})
    else:
        print("No solution found")

if __name__ == "__main__":
    main()