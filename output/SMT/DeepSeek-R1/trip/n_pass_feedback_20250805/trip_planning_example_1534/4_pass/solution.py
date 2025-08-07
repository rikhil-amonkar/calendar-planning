from z3 import *

def main():
    # Input data
    cities_to_visit = ["Paris", "Florence", "Barcelona", "Tallinn", "Vilnius", "Warsaw", "Venice", "Amsterdam", "Hamburg", "Salzburg"]
    min_days = {
        "Paris": 1, "Florence": 2, "Barcelona": 3, "Tallinn": 1, "Vilnius": 1, 
        "Warsaw": 2, "Venice": 1, "Amsterdam": 2, "Hamburg": 3, "Salzburg": 2
    }
    max_days = {
        "Paris": 3, "Florence": 5, "Barcelona": 5, "Tallinn": 3, "Vilnius": 3, 
        "Warsaw": 4, "Venice": 3, "Amsterdam": 4, "Hamburg": 5, "Salzburg": 4
    }
    total_days = 25
    num_stays = len(cities_to_visit)
    
    city_to_int = {city: idx for idx, city in enumerate(cities_to_visit)}
    int_to_city = {idx: city for idx, city in enumerate(cities_to_visit)}
    
    s = Solver()
    
    # Create Z3 variables
    starts = [Int(f's_{i}') for i in range(num_stays)]
    ends = [Int(f'e_{i}') for i in range(num_stays)]
    cities = [Int(f'c_{i}') for i in range(num_stays)]
    
    # Each city must be one of the cities to visit
    for i in range(num_stays):
        s.add(Or([cities[i] == city_to_int[city] for city in cities_to_visit]))
    
    # Each city visited exactly once
    s.add(Distinct(cities))
    
    # First stay starts on day 1
    s.add(starts[0] == 1)
    # Last stay ends on day 25
    s.add(ends[num_stays - 1] == total_days)
    
    # Consecutive stays have no gaps: next starts immediately after previous ends
    for i in range(num_stays - 1):
        s.add(starts[i + 1] == ends[i] + 1)
    
    # Duration constraints for each stay
    for i in range(num_stays):
        duration = ends[i] - starts[i] + 1
        city = cities[i]
        for c in cities_to_visit:
            c_idx = city_to_int[c]
            s.add(Implies(city == c_idx, And(duration >= min_days[c], duration <= max_days[c])))
    
    # Solve the constraints
    if s.check() == sat:
        model = s.model()
        plan = []
        for i in range(num_stays):
            s_val = model.evaluate(starts[i]).as_long()
            e_val = model.evaluate(ends[i]).as_long()
            c_val = model.evaluate(cities[i]).as_long()
            city_name = int_to_city[c_val]
            day_range = f"Day {s_val}-{e_val}"
            plan.append({'day_range': day_range, 'place': city_name})
        
        print(f"Plan found: {plan}")
    else:
        print("No valid plan found")

if __name__ == '__main__':
    main()