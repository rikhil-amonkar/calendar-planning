from z3 import *
import json

def main():
    # Represent cities as integers for simplicity
    cities = ["Paris", "Florence", "Vienna", "Porto", "Munich", "Nice", "Warsaw"]
    city_to_int = {city: i for i, city in enumerate(cities)}
    int_to_city = {i: city for i, city in enumerate(cities)}
    
    # Direct flight connections (bidirectional)
    direct_flights = [
        ("Florence", "Vienna"), ("Paris", "Warsaw"), ("Munich", "Vienna"),
        ("Porto", "Vienna"), ("Warsaw", "Vienna"), ("Florence", "Munich"),
        ("Munich", "Warsaw"), ("Munich", "Nice"), ("Paris", "Florence"),
        ("Warsaw", "Nice"), ("Porto", "Munich"), ("Porto", "Nice"),
        ("Paris", "Vienna"), ("Nice", "Vienna"), ("Porto", "Paris"),
        ("Paris", "Nice"), ("Paris", "Munich"), ("Porto", "Warsaw")
    ]
    
    # Create flight matrix
    flight_matrix = [[False]*7 for _ in range(7)]
    for city1, city2 in direct_flights:
        i1, i2 = city_to_int[city1], city_to_int[city2]
        flight_matrix[i1][i2] = True
        flight_matrix[i2][i1] = True
    
    # Create Z3 variables
    start_city = [Int(f'start_{i}') for i in range(20)]  # Day 1 to 20
    end_city = [Int(f'end_{i}') for i in range(20)]      # Day 1 to 20
    
    s = Solver()
    
    # City IDs must be between 0-6
    for i in range(20):
        s.add(And(start_city[i] >= 0, start_city[i] < 7))
        s.add(And(end_city[i] >= 0, end_city[i] < 7))
    
    # Continuity constraint
    for i in range(19):
        s.add(end_city[i] == start_city[i+1])
    
    # Flight validity
    for i in range(20):
        current_start = start_city[i]
        current_end = end_city[i]
        # Either stay in same city or direct flight exists
        s.add(Or(
            current_start == current_end,
            # Check flight matrix
            *[And(current_start == j, current_end == k) 
              for j in range(7) for k in range(7) if flight_matrix[j][k]]
        ))
    
    # Fixed event constraints
    porto_id = city_to_int["Porto"]
    warsaw_id = city_to_int["Warsaw"]
    vienna_id = city_to_int["Vienna"]
    
    # Porto: Days 1-3 (index 0-2)
    for i in [0, 1, 2]:
        s.add(Or(start_city[i] == porto_id, end_city[i] == porto_id))
    
    # Warsaw: Days 13-15 (index 12-14)
    for i in [12, 13, 14]:
        s.add(Or(start_city[i] == warsaw_id, end_city[i] == warsaw_id))
    
    # Vienna: Days 19-20 (index 18-19)
    for i in [18, 19]:
        s.add(Or(start_city[i] == vienna_id, end_city[i] == vienna_id))
    
    # Total days per city
    required_days = {
        "Paris": 5,
        "Florence": 3,  # Note: Typo in city name (should match 'Florence' in cities list)
        "Vienna": 2,
        "Porto": 3,
        "Munich": 5,
        "Nice": 5,
        "Warsaw": 3
    }
    
    for city, days in required_days.items():
        if city == "Florence":  # Handle the typo
            city_id = city_to_int["Florence"]
        else:
            city_id = city_to_int[city]
        total = 0
        for i in range(20):
            total += If(Or(start_city[i] == city_id, end_city[i] == city_id), 1, 0)
        s.add(total == days)
    
    # Solve and output
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(20):
            start_val = m.eval(start_city[day]).as_long()
            end_val = m.eval(end_city[day]).as_long()
            places = [int_to_city[start_val]]
            if start_val != end_val:
                places.append(int_to_city[end_val])
            itinerary.append({
                "day": day + 1,
                "place": sorted(places)
            })
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()