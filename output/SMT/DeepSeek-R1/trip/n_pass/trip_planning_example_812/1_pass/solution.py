from z3 import *
import json

def main():
    # Define city names and indices
    cities = ["Porto", "Paris", "Florence", "Vienna", "Munich", "Nice", "Warsaw"]
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    
    # Required days per city
    req_days = {
        "Porto": 3,
        "Paris": 5,
        "Florence": 3,
        "Vienna": 2,
        "Munich": 5,
        "Nice": 5,
        "Warsaw": 3
    }
    req_days_index = [req_days[city] for city in cities]
    
    # Define direct flights as set of tuples (min_city_idx, max_city_idx)
    flight_pairs_str = [
        ("Florence", "Vienna"),
        ("Paris", "Warsaw"),
        ("Munich", "Vienna"),
        ("Porto", "Vienna"),
        ("Warsaw", "Vienna"),
        ("Florence", "Munich"),
        ("Munich", "Warsaw"),
        ("Munich", "Nice"),
        ("Paris", "Florence"),
        ("Warsaw", "Nice"),
        ("Porto", "Munich"),
        ("Porto", "Nice"),
        ("Paris", "Vienna"),
        ("Nice", "Vienna"),
        ("Porto", "Paris"),
        ("Paris", "Nice"),
        ("Paris", "Munich"),
        ("Porto", "Warsaw")
    ]
    allowed_pairs = set()
    for u, v in flight_pairs_str:
        idx_u = city_to_index[u]
        idx_v = city_to_index[v]
        if idx_u < idx_v:
            pair = (idx_u, idx_v)
        else:
            pair = (idx_v, idx_u)
        allowed_pairs.add(pair)
    
    # Create Z3 solver and variables
    s = Solver()
    n_stays = 7
    
    # Arrays for stay variables
    stay_city = [Int(f'stay_city_{i}') for i in range(n_stays)]
    stay_start = [Int(f'stay_start_{i}') for i in range(n_stays)]
    stay_end = [Int(f'stay_end_{i}') for i in range(n_stays)]
    
    # Constraints for each stay
    for i in range(n_stays):
        s.add(stay_start[i] >= 1)
        s.add(stay_end[i] <= 20)
        s.add(stay_start[i] <= stay_end[i])
        # Length of stay = req_days for the city
        s.add(stay_end[i] - stay_start[i] + 1 == req_days_index[stay_city[i]])
    
    # Distinct cities
    s.add(Distinct(stay_city))
    for i in range(n_stays):
        s.add(And(stay_city[i] >= 0, stay_city[i] <= 6))
    
    # Fixed stays
    s.add(stay_city[0] == city_to_index["Porto"])
    s.add(stay_start[0] == 1)
    s.add(stay_end[0] == 3)
    
    s.add(stay_city[6] == city_to_index["Vienna"])
    s.add(stay_start[6] == 19)
    s.add(stay_end[6] == 20)
    
    # Warsaw (index 6) must be one of the stays and fixed to 13-15
    warsaw_idx = city_to_index["Warsaw"]
    for i in range(1, 6):  # Warsaw cannot be first or last stay
        s.add(Implies(stay_city[i] == warsaw_idx, 
                      And(stay_start[i] == 13, stay_end[i] == 15)))
    # Ensure Warsaw is in the itinerary
    s.add(Or([stay_city[i] == warsaw_idx for i in range(1, 6)]))
    
    # Consecutive stays: end[i] == start[i+1]
    for i in range(n_stays - 1):
        s.add(stay_end[i] == stay_start[i+1])
    
    # Flight connectivity: consecutive cities must have a direct flight
    for i in range(n_stays - 1):
        u = stay_city[i]
        v = stay_city[i+1]
        # Create a condition for each allowed pair
        conds = []
        for pair in allowed_pairs:
            conds.append(Or(And(u == pair[0], v == pair[1]), And(u == pair[1], v == pair[0])))
        s.add(Or(conds))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        # Extract values
        stay_city_val = [m.eval(stay_city[i]).as_long() for i in range(n_stays)]
        stay_start_val = [m.eval(stay_start[i]).as_long() for i in range(n_stays)]
        stay_end_val = [m.eval(stay_end[i]).as_long() for i in range(n_stays)]
        
        # Build itinerary list
        itinerary = []
        for i in range(n_stays):
            city_name = cities[stay_city_val[i]]
            start = stay_start_val[i]
            end = stay_end_val[i]
            
            # Add the continuous stay
            if start == end:
                day_range_str = f"Day {start}"
                itinerary.append({"day_range": day_range_str, "place": city_name})
            else:
                day_range_str = f"Day {start}-{end}"
                itinerary.append({"day_range": day_range_str, "place": city_name})
            
            # If not the last stay, add the flight day records: departure and arrival
            if i < n_stays - 1:
                # Last day of current stay is the flight day (departure)
                day = end
                itinerary.append({"day_range": f"Day {day}", "place": city_name})
                # Arrival city on the same day
                next_city = cities[stay_city_val[i+1]]
                itinerary.append({"day_range": f"Day {day}", "place": next_city})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()