from z3 import *
import json

def main():
    cities_dict = {
        "Bucharest": 0,
        "Venice": 1,
        "Prague": 2,
        "Frankfurt": 3,
        "Zurich": 4,
        "Florence": 5,
        "Tallinn": 6
    }
    city_names = {v: k for k, v in cities_dict.items()}
    
    edges = [
        (2, 6), (6, 2),
        (2, 4), (4, 2),
        (5, 2), (2, 5),
        (3, 0), (0, 3),
        (3, 1), (1, 3),
        (2, 0), (0, 2),
        (0, 4), (4, 0),
        (6, 3), (3, 6),
        (4, 5), (5, 4),
        (3, 4), (4, 3),
        (4, 1), (1, 4),
        (5, 3), (3, 5),
        (2, 3), (3, 2),
        (6, 4), (4, 6)
    ]
    
    required_days = [3, 5, 4, 5, 5, 5, 5]
    
    cities = [Int(f'city_{i}') for i in range(27)]
    s = Solver()
    
    for c in cities:
        s.add(c >= 0, c <= 6)
    
    for i in range(1, 27):
        valid_transitions = [cities[i-1] == cities[i]]
        for a, b in edges:
            valid_transitions.append(And(cities[i-1] == a, cities[i] == b))
        s.add(Or(valid_transitions))
    
    for c in range(7):
        total = 0
        for i in range(1, 27):
            total += If(Or(cities[i-1] == c, cities[i] == c), 1, 0)
        s.add(total == required_days[c])
    
    venice_days = []
    for day in range(22, 27):
        venice_days.append(Or(cities[day-1] == 1, cities[day] == 1))
    s.add(Or(venice_days))
    
    frankfurt_days = []
    for day in range(12, 17):
        frankfurt_days.append(Or(cities[day-1] == 3, cities[day] == 3))
    s.add(Or(frankfurt_days))
    
    tallinn_days = []
    for day in range(8, 13):
        tallinn_days.append(Or(cities[day-1] == 6, cities[day] == 6))
    s.add(Or(tallinn_days))
    
    if s.check() == sat:
        model = s.model()
        presence = {c: set() for c in range(7)}
        
        # Check start of day 1 (city0)
        start_city = model[cities[0]].as_long()
        presence[start_city].add(1)
        
        # Check each day (1-26)
        for day in range(1, 27):
            start_city = model[cities[day-1]].as_long()
            end_city = model[cities[day]].as_long()
            presence[start_city].add(day)
            presence[end_city].add(day)
        
        # Create itinerary
        itinerary = []
        for c in range(7):
            if presence[c]:
                min_day = min(presence[c])
                max_day = max(presence[c])
                itinerary.append({
                    'day_range': f'Day {min_day}-{max_day}',
                    'place': city_names[c]
                })
        
        # Sort itinerary by starting day
        itinerary.sort(key=lambda x: int(x['day_range'].split('-')[0].split()[1]))
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()