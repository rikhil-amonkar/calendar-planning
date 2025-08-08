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
    
    # Direct flight edges (undirected)
    edges = [
        (0, 2), (0, 1), (2, 1), (1, 3), (2, 4), (4, 1), (0, 3)
    ]
    allowed_pairs = []
    for (a, b) in edges:
        allowed_pairs.append((a, b))
        allowed_pairs.append((b, a))
    
    # Create solver and variables
    s = Solver()
    stay = [Int(f'stay_{i}') for i in range(21)]  # 0-indexed: stay[0] is day1, stay[20] is day21
    fly = [Bool(f'fly_{i}') for i in range(20)]    # fly[0] is flight at end of day1, fly[19] is at end of day20
    
    # Constraints: stay within city indices
    for i in range(21):
        s.add(stay[i] >= 0, stay[i] <= 4)
    
    # Flight constraints
    for i in range(20):
        s.add(If(
            fly[i],
            Or([And(stay[i] == a, stay[i+1] == b) for (a, b) in allowed_pairs]),
            stay[i] == stay[i+1]
        ))
    
    # Total flights must be 4
    total_flights = Sum([If(fly[i], 1, 0) for i in range(20)])
    s.add(total_flights == 4)
    
    # Per city total days constraints
    for city, required in [(0, 3), (1, 7), (2, 7), (3, 6), (4, 2)]:
        base_days = Sum([If(stay[i] == city, 1, 0) for i in range(21)])
        flight_arrivals = Sum([If(And(fly[i], stay[i+1] == city), 1, 0) for i in range(20)])
        s.add(base_days + flight_arrivals == required)
    
    # Event constraints
    # Manchester: at least one day in [1,3] (days 1,2,3)
    cond_wedding = Or(
        Or(stay[0] == 0, And(fly[0], stay[1] == 0)),  # day1
        Or(stay[1] == 0, And(fly[1], stay[2] == 0)),  # day2
        Or(stay[2] == 0, And(fly[2], stay[3] == 0))   # day3
    )
    s.add(cond_wedding)
    
    # Venice: at least one day in [3,9] (days 3 to 9)
    cond_workshop = Or(
        [Or(stay[d-1] == 2, And(fly[d-1], stay[d] == 2)) for d in range(3, 10)
    )
    s.add(cond_workshop)
    
    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(1, 22):  # days 1 to 21
            idx = day - 1
            city_val = m.eval(stay[idx]).as_long()
            city_name = rev_cities[city_val]
            itinerary.append({"day": day, "place": city_name})
        
        result = {'itinerary': itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()