from z3 import *
import json

def main():
    cities = ["Brussels", "Helsinki", "Split", "Dubrovnik", "Istanbul", "Milan", "Vilnius", "Frankfurt"]
    n_cities = len(cities)
    n_days = 22
    
    # Create city indices
    Brussels_idx = cities.index("Brussels")
    Helsinki_idx = cities.index("Helsinki")
    Split_idx = cities.index("Split")
    Dubrovnik_idx = cities.index("Dubrovnik")
    Istanbul_idx = cities.index("Istanbul")
    Milan_idx = cities.index("Milan")
    Vilnius_idx = cities.index("Vilnius")
    Frankfurt_idx = cities.index("Frankfurt")
    
    # Flight connections
    bidirectional_edges = [
        ("Milan", "Frankfurt"),
        ("Split", "Frankfurt"),
        ("Milan", "Split"),
        ("Brussels", "Vilnius"),
        ("Brussels", "Helsinki"),
        ("Istanbul", "Brussels"),
        ("Milan", "Vilnius"),
        ("Brussels", "Milan"),
        ("Istanbul", "Helsinki"),
        ("Helsinki", "Vilnius"),
        ("Helsinki", "Dubrovnik"),
        ("Split", "Vilnius"),
        ("Istanbul", "Milan"),
        ("Helsinki", "Frankfurt"),
        ("Istanbul", "Vilnius"),
        ("Split", "Helsinki"),
        ("Milan", "Helsinki"),
        ("Istanbul", "Frankfurt"),
        ("Dubrovnik", "Frankfurt"),
        ("Frankfurt", "Vilnius")
    ]
    
    directed_edges = [
        ("Dubrovnik", "Istanbul"),
        ("Brussels", "Frankfurt")
    ]
    
    # Create set of directed flights
    directed_flights_set = set()
    for (a, b) in bidirectional_edges:
        i = cities.index(a)
        j = cities.index(b)
        directed_flights_set.add((i, j))
        directed_flights_set.add((j, i))
    for (a, b) in directed_edges:
        i = cities.index(a)
        j = cities.index(b)
        directed_flights_set.add((i, j))
    
    # Initialize solver
    s = Solver()
    
    # Morning and evening city for each day
    city_morning = [Int(f'city_morning_{d}') for d in range(n_days)]
    city_evening = [Int(f'city_evening_{d}') for d in range(n_days)]
    fly = [Bool(f'fly_{d}') for d in range(n_days)]  # True if flying during day d
    
    # City must be valid index
    for d in range(n_days):
        s.add(city_morning[d] >= 0, city_morning[d] < n_cities)
        s.add(city_evening[d] >= 0, city_evening[d] < n_cities)
    
    # Day 1 starts in Istanbul
    s.add(city_morning[0] == Istanbul_idx)
    
    # Consistency between consecutive days: next morning is previous evening
    for d in range(1, n_days):
        s.add(city_morning[d] == city_evening[d-1])
    
    # Flight constraints
    for d in range(n_days):
        # If flying, evening city differs from morning city and flight is valid
        s.add(fly[d] == (city_morning[d] != city_evening[d]))
        valid_flight = Or([And(city_morning[d] == i, city_evening[d] == j) for (i, j) in directed_flights_set])
        s.add(Implies(fly[d], valid_flight))
    
    # Event constraints
    # Istanbul: full days for days 1-4 (indices 0-3)
    for d in range(4):  # Days 1-4 (indices 0 to 3)
        s.add(city_morning[d] == Istanbul_idx)
        s.add(city_evening[d] == Istanbul_idx)
    
    # Frankfurt: full days for days 16-17 (indices 15-16), and morning only on day 18 (index 17)
    s.add(city_morning[15] == Frankfurt_idx, city_evening[15] == Frankfurt_idx)  # Day 16
    s.add(city_morning[16] == Frankfurt_idx, city_evening[16] == Frankfurt_idx)  # Day 17
    s.add(city_morning[17] == Frankfurt_idx)  # Day 18 morning
    
    # Vilnius: evening on day 18 (index 17) and full days for days 19-22 (indices 18-21)
    s.add(city_evening[17] == Vilnius_idx)  # Day 18 evening
    for d in range(18, 22):  # Days 19-22 (indices 18 to 21)
        s.add(city_morning[d] == Vilnius_idx)
        s.add(city_evening[d] == Vilnius_idx)
    
    # Duration constraints (count a day if either morning or evening is in the city)
    total_days = [0] * n_cities
    for i in range(n_cities):
        total_days[i] = Sum([If(Or(city_morning[d] == i, city_evening[d] == i), 1, 0) for d in range(n_days)])
    s.add(total_days[Brussels_idx] == 3)
    s.add(total_days[Helsinki_idx] == 3)
    s.add(total_days[Split_idx] == 4)
    s.add(total_days[Dubrovnik_idx] == 2)
    s.add(total_days[Istanbul_idx] == 5)
    s.add(total_days[Milan_idx] == 4)
    s.add(total_days[Vilnius_idx] == 5)
    s.add(total_days[Frankfurt_idx] == 3)
    
    # Total flights should be 7
    s.add(Sum([If(fly[d], 1, 0) for d in range(n_days)]) == 7)
    
    # Solve and output
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for d in range(n_days):
            morning_city = cities[m.eval(city_morning[d]).as_long()]
            evening_city = cities[m.eval(city_evening[d]).as_long()]
            if morning_city == evening_city:
                itinerary.append({"day": d+1, "place": morning_city})
            else:
                itinerary.append({"day": d+1, "place": f"{morning_city} (morning) -> {evening_city} (evening)"})
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()