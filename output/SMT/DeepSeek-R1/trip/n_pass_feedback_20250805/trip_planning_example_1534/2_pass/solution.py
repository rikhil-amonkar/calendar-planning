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
    adjacencies = {
        "Paris": ["Brussels", "Strasbourg", "Bordeaux", "Nantes", "Lyon", "Lille"],
        "Florence": ["Milan", "Rome", "Bologna", "Venice"],
        "Barcelona": ["Valencia", "Zaragoza", "Toulouse"],
        "Tallinn": ["Helsinki", "Riga", "Saint Petersburg"],
        "Vilnius": ["Riga", "Warsaw", "Kaunas", "Daugavpils"],
        "Warsaw": ["Berlin", "Prague", "Krakow", "Vilnius"],
        "Venice": ["Milan", "Florence", "Verona", "Trieste"],
        "Amsterdam": ["Brussels", "Hamburg", "Cologne", "Rotterdam"],
        "Hamburg": ["Bremen", "Hannover", "Berlin", "Amsterdam", "Copenhagen"],
        "Salzburg": ["Munich", "Vienna", "Innsbruck", "Graz"]
    }
    total_days = 25

    num_stays = len(cities_to_visit)
    city_to_int = {city: idx for idx, city in enumerate(cities_to_visit)}
    int_to_city = {idx: city for city, idx in city_to_int.items()}

    s = Solver()

    # Create Z3 variables for start and end days of each stay, and the city for each stay
    starts = [Int(f's_{i}') for i in range(num_stays)]
    ends = [Int(f'e_{i}') for i in range(num_stays)]
    cities = [Int(f'c_{i}') for i in range(num_stays)]

    # Domain constraints for cities: each must be one of the cities in cities_to_visit
    for i in range(num_stays):
        s.add(Or([cities[i] == city_to_int[city] for city in cities_to_visit]))
    
    # Each city must appear exactly once
    s.add(Distinct(cities))

    # First stay starts on day 1
    s.add(starts[0] == 1)
    # Last stay ends on day 25
    s.add(ends[num_stays-1] == total_days)

    # Order of stays: each stay starts after the previous one ends (accounting for travel)
    for i in range(num_stays-1):
        s.add(starts[i+1] > ends[i])

    # Duration constraints for each stay
    for i in range(num_stays):
        duration = ends[i] - starts[i] + 1
        city_name = int_to_city[cities[i].as_long()] if isinstance(cities[i], int) else None
        if city_name is None:
            # If cities[i] is a Z3 variable, we use a lookup
            s.add(Or([And(cities[i] == city_to_int[city], 
                      min_days[city] <= duration, 
                      duration <= max_days[city]) for city in cities_to_visit]))
        else:
            s.add(min_days[city_name] <= duration)
            s.add(duration <= max_days[city_name])

    # Adjacency constraints between consecutive stays
    for i in range(num_stays - 1):
        # Create a condition that checks if the current city and next city are adjacent
        adjacent_cond = Or([And(cities[i] == city_to_int[city1], cities[i+1] == city_to_int[city2]) 
                           for city1 in adjacencies 
                           for city2 in adjacencies[city1] 
                           if city1 in city_to_int and city2 in city_to_int])
        
        # If adjacent, next stay starts the day after current stay ends (adj=1), else two days after (adj=2)
        adj = If(adjacent_cond, 1, 2)
        s.add(starts[i+1] == ends[i] + adj)

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
        
        # Output the plan
        print(f"Plan found: {plan}")
    else:
        print("No valid plan found")

if __name__ == '__main__':
    main()