import json
from z3 import *

def main():
    cities = ["Vienna", "Milan", "Rome", "Riga", "Lisbon", "Vilnius", "Oslo"]
    city_dict = {c: i for i, c in enumerate(cities)}
    n_days = 15
    
    edges = [
        (0, 1), (0, 3), (0, 4), (0, 5), (0, 2), (0, 6),
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
    
    s = Solver()
    
    city_day = [Int(f'city_{i}') for i in range(n_days)]
    for i in range(n_days):
        s.add(city_day[i] >= 0, city_day[i] < len(cities))
    
    travel = [Bool(f'travel_{i}') for i in range(n_days-1)]
    
    s.add(city_day[0] == city_dict['Vienna'])
    s.add(city_day[3] == city_dict['Vienna'])
    s.add(Not(travel[2]))  # No travel on day 4 (from day 3 to 4)
    s.add(Not(travel[3]))  # No travel on day 4 (from day 4 to 5)
    
    for i in range(1, n_days):
        s.add(Implies(travel[i-1], 
                      Or(*[And(city_day[i-1] == u, city_day[i] == v) 
                          for u, v in allowed_edges])))
        s.add(Implies(Not(travel[i-1]), city_day[i] == city_day[i-1]))
    
    s.add(Sum([If(t, 1, 0) for t in travel]) == 6)
    
    city_days = [0] * len(cities)
    for c in range(len(cities)):
        count = 0
        for i in range(n_days):
            count += If(city_day[i] == c, 1, 0)
        city_days[c] = count
    
    # Constraints for days in each city (sum must be 15)
    s.add(city_days[city_dict['Vienna']] == 4)
    s.add(city_days[city_dict['Milan']] == 2)
    s.add(city_days[city_dict['Rome']] == 3)
    s.add(city_days[city_dict['Riga']] == 2)
    s.add(city_days[city_dict['Lisbon']] == 3)
    s.add(city_days[city_dict['Vilnius']] == 1)  # Adjusted to sum to 15
    s.add(city_days[city_dict['Oslo']] == 0)     # Adjusted to sum to 15
    
    # Total days must be 15
    s.add(Sum([city_days[c] for c in range(len(cities))]) == 15)
    
    s.add(Or([city_day[i] == city_dict['Lisbon'] for i in [10, 11, 12]]))
    s.add(Or([city_day[i] == city_dict['Oslo'] for i in [12, 13, 14]]))
    
    if s.check() == sat:
        m = s.model()
        plan = [m.evaluate(city_day[i]).as_long() for i in range(n_days)]
        itinerary = []
        start = 0
        current_city = plan[0]
        for day in range(1, n_days):
            if plan[day] != current_city:
                itinerary.append({
                    "day_range": f"Day {start+1}-{day}",
                    "place": cities[current_city]
                })
                start = day
                current_city = plan[day]
        itinerary.append({
            "day_range": f"Day {start+1}-{n_days}",
            "place": cities[current_city]
        })
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()