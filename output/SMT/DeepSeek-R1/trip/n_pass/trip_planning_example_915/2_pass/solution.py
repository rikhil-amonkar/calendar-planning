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
        (4, 5),
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
        current_edges = []
        for a, b in edges:
            current_edges.append(And(cities[i-1] == a, cities[i] == b))
        s.add(Or(cities[i-1] == cities[i], Or(current_edges)))
    
    for c in range(7):
        total = 0
        for i in range(1, 27):
            total += If(Or(cities[i-1] == c, cities[i] == c), 1, 0)
        s.add(total == required_days[c])
    
    venice_days = []
    for i in [22, 23, 24, 25, 26]:
        venice_days.append(Or(cities[i-1] == 1, cities[i] == 1))
    s.add(Or(venice_days))
    
    frankfurt_days = []
    for i in [12, 13, 14, 15, 16]:
        frankfurt_days.append(Or(cities[i-1] == 3, cities[i] == 3))
    s.add(Or(frankfurt_days))
    
    tallinn_days = []
    for i in [8, 9, 10, 11, 12]:
        tallinn_days.append(Or(cities[i-1] == 6, cities[i] == 6))
    s.add(Or(tallinn_days))
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, 27):
            city_val = model[cities[day]].as_long()
            itinerary.append({"day": day, "place": city_names[city_val]})
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()