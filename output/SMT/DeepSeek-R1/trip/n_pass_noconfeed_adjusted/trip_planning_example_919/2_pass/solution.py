import json
from z3 import *

def main():
    # Define cities
    cities = ["Vienna", "Milan", "Rome", "Riga", "Lisbon", "Vilnius", "Oslo"]
    city_dict = {c: i for i, c in enumerate(cities)}
    n_days = 15
    
    # Direct flights (bidirectional)
    edges = [
        (0, 1), (0, 5), (0, 4), (0, 3), (0, 2), (0, 6),
        (1, 3), (1, 6), (1, 5), (1, 4),
        (2, 6), (2, 3), (2, 4),
        (3, 5), (3, 4), (3, 6),
        (4, 6),
        (5, 6), (5, 3), (5, 1)
    ]
    allowed_edges = set()
    for u, v in edges:
        allowed_edges.add((u, v))
        allowed_edges.add((v, u))
    
    # Initialize solver
    s = Solver()
    
    # Variables for each day: city we sleep in
    city_day = [Int(f'city_day_{i}') for i in range(n_days)]
    for i in range(n_days):
        s.add(And(city_day[i] >= 0, city_day[i] < len(cities)))
    
    # Variables for travel (day i involves travel from previous city)
    travel = [Bool(f'travel_{i}') for i in range(1, n_days)]
    
    # Fixed constraints: Day 1 and Day 4 in Vienna without travel
    s.add(city_day[0] == city_dict['Vienna'])
    s.add(city_day[3] == city_dict['Vienna'])
    s.add(Not(travel[0]))  # Day 1 no travel
    s.add(Not(travel[3]))  # Day 4 no travel
    
    # Travel constraints
    for i in range(1, n_days):
        # If travel, then direct flight exists between previous and current city
        s.add(Implies(travel[i-1], 
                      Or(*[And(city_day[i-1] == u, city_day[i] == v) 
                          for u, v in allowed_edges if u != v])))
        # If no travel, then same city as previous day
        s.add(Implies(Not(travel[i-1]), city_day[i] == city_day[i-1]))
    
    # Total travel days (6)
    s.add(Sum([If(travel_i, 1, 0) for travel_i in travel]) == 6)
    
    # Count days per city (including travel days)
    city_days = [0] * len(cities)
    for c in range(len(cities)):
        # Day 1 counts if sleeping in city c
        count = If(city_day[0] == c, 1, 0)
        # Days 2-15: sleeping in city c
        for i in range(1, n_days):
            count += If(city_day[i] == c, 1, 0)
        # Travel days: morning in city c (if traveled from c)
        for i in range(1, n_days):
            count += If(And(travel[i-1], city_day[i-1] == c), 1, 0)
        city_days[c] = count
    
    # Required days per city
    s.add(city_days[city_dict['Vienna']] == 4)
    s.add(city_days[city_dict['Milan']] == 2)
    s.add(city_days[city_dict['Rome']] == 3)
    s.add(city_days[city_dict['Riga']] == 2)
    s.add(city_days[city_dict['Lisbon']] == 3)
    s.add(city_days[city_dict['Vilnius']] == 4)
    s.add(city_days[city_dict['Oslo']] == 3)
    
    # Lisbon between day 11-13 (1-indexed days 11,12,13)
    s.add(Or(city_day[9] == city_dict['Lisbon'], city_day[10] == city_dict['Lisbon'], city_day[11] == city_dict['Lisbon'], city_day[12] == city_dict['Lisbon']))
    
    # Oslo between day 13-15 (1-indexed days 13,14,15)
    s.add(Or(city_day[11] == city_dict['Oslo'], city_day[12] == city_dict['Oslo'], city_day[13] == city_dict['Oslo'], city_day[14] == city_dict['Oslo']))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        # Get assigned cities for each day
        assigned_cities = []
        for i in range(n_days):
            val = m.evaluate(city_day[i])
            assigned_cities.append(int(val.as_string()))
        
        # Convert to city names
        city_names = [cities[idx] for idx in assigned_cities]
        
        # Group consecutive days with same city
        itinerary = []
        start = 0
        current_city = city_names[0]
        for day in range(1, n_days):
            if city_names[day] != current_city:
                end = day
                itinerary.append({
                    "day_range": f"Day {start+1}-{end}",
                    "place": current_city
                })
                start = day
                current_city = city_names[day]
        itinerary.append({
            "day_range": f"Day {start+1}-{n_days}",
            "place": current_city
        })
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()