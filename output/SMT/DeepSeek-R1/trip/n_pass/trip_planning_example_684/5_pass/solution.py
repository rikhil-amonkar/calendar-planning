from z3 import *
import json

def main():
    # City mapping to integers
    cities = ['Amsterdam', 'Edinburgh', 'Brussels', 'Vienna', 'Berlin', 'Reykjavik']
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for city, idx in city_to_int.items()}
    
    # Required days per city
    required_days = {
        'Amsterdam': 4,
        'Edinburgh': 5,
        'Brussels': 5,
        'Vienna': 5,
        'Berlin': 4,
        'Reykjavik': 5
    }
    req_days_int = [required_days[city] for city in cities]
    
    # Direct flights matrix (symmetric)
    flight_matrix = [
        [0, 1, 1, 1, 1, 1],  # Amsterdam
        [1, 0, 1, 0, 1, 0],  # Edinburgh
        [1, 1, 0, 1, 1, 1],  # Brussels
        [1, 0, 1, 0, 1, 1],  # Vienna
        [1, 1, 1, 1, 0, 1],  # Berlin
        [1, 0, 1, 1, 1, 0]   # Reykjavik
    ]
    
    n_days = 23
    s = Solver()
    
    # Day variables: 0-5 for each city
    c = [Int(f'c_{i}') for i in range(n_days)]
    
    # Each day must be a valid city (0-5)
    for i in range(n_days):
        s.add(And(c[i] >= 0, c[i] < 6))
    
    # Flight constraints between consecutive days
    for i in range(n_days - 1):
        current = c[i]
        next_ = c[i+1]
        # Allow staying in same city or direct flight
        s.add(Or(
            current == next_,
            flight_matrix[current][next_] == 1
        ))
    
    # Total days per city constraint
    for city_int in range(6):
        count = Sum([If(c[i] == city_int, 1, 0) for i in range(n_days)])
        s.add(count == req_days_int[city_int])
    
    # Amsterdam must be visited between days 5-8 (0-indexed days 4-7)
    s.add(Or(
        c[4] == city_to_int['Amsterdam'],  # Day 5
        c[5] == city_to_int['Amsterdam'],  # Day 6
        c[6] == city_to_int['Amsterdam'],  # Day 7
        c[7] == city_to_int['Amsterdam']   # Day 8
    ))
    
    # Berlin must be visited between days 16-19 (0-indexed days 15-18)
    s.add(Or(
        c[15] == city_to_int['Berlin'],  # Day 16
        c[16] == city_to_int['Berlin'],  # Day 17
        c[17] == city_to_int['Berlin'],  # Day 18
        c[18] == city_to_int['Berlin']   # Day 19
    ))
    
    # Reykjavik must be visited between days 12-16 (0-indexed days 11-15)
    s.add(Or(
        c[11] == city_to_int['Reykjavik'],  # Day 12
        c[12] == city_to_int['Reykjavik'],  # Day 13
        c[13] == city_to_int['Reykjavik'],  # Day 14
        c[14] == city_to_int['Reykjavik'],  # Day 15
        c[15] == city_to_int['Reykjavik']   # Day 16
    ))
    
    # Solve and output itinerary
    if s.check() == sat:
        m = s.model()
        day_assignments = [m.eval(c[i]).as_long() for i in range(n_days)]
        itinerary = []
        current_city = int_to_city[day_assignments[0]]
        start_day = 1
        
        for day in range(1, n_days):
            city = int_to_city[day_assignments[day]]
            if city != current_city:
                itinerary.append({
                    "day_range": f"Day {start_day}-{day}",
                    "place": current_city
                })
                current_city = city
                start_day = day + 1
        
        itinerary.append({
            "day_range": f"Day {start_day}-{n_days}",
            "place": current_city
        })
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()