from z3 import *
import json

def main():
    cities = ['Oslo', 'Reykjavik', 'Stockholm', 'Munich', 'Frankfurt', 'Barcelona', 'Bucharest', 'Split']
    CitySort, city_consts = EnumSort('City', cities)
    city_dict = {name: const for name, const in zip(cities, city_consts)}
    
    direct_flight_pairs = [
        ("Reykjavik", "Munich"), ("Munich", "Frankfurt"), ("Split", "Oslo"),
        ("Reykjavik", "Oslo"), ("Bucharest", "Munich"), ("Oslo", "Frankfurt"),
        ("Bucharest", "Barcelona"), ("Barcelona", "Frankfurt"), ("Reykjavik", "Frankfurt"),
        ("Barcelona", "Stockholm"), ("Barcelona", "Reykjavik"), ("Stockholm", "Reykjavik"),
        ("Barcelona", "Split"), ("Bucharest", "Oslo"), ("Bucharest", "Frankfurt"),
        ("Split", "Stockholm"), ("Barcelona", "Oslo"), ("Stockholm", "Munich"),
        ("Stockholm", "Oslo"), ("Split", "Frankfurt"), ("Barcelona", "Munich"),
        ("Stockholm", "Frankfurt"), ("Munich", "Oslo"), ("Split", "Munich")
    ]
    
    allowed_pairs = set()
    for a, b in direct_flight_pairs:
        a_const = city_dict[a]
        b_const = city_dict[b]
        allowed_pairs.add((a_const, b_const))
        allowed_pairs.add((b_const, a_const))
    
    E = [Const('E%d' % i, CitySort) for i in range(21)]
    s = Solver()
    
    # Start and end constraints
    s.add(E[0] == E[1])       # First full day in initial city
    s.add(E[19] == E[20])     # Last full day in final city
    
    # Flight constraints
    for d in range(1, 21):
        prev = E[d-1]
        curr = E[d]
        flight_valid = Or([And(prev == a, curr == b) for (a, b) in allowed_pairs])
        s.add(If(prev != curr, flight_valid, True))
    
    # Total days per city
    for city, days in zip(cities, [2, 5, 4, 4, 4, 3, 2, 3]):
        c = city_dict[city]
        count = 0
        for d in range(1, 21):
            count += If(Or(E[d-1] == c, E[d] == c), 1, 0)
        s.add(count == days)
    
    # Event constraints
    oslo = city_dict['Oslo']
    s.add(Or(E[15] == oslo, E[16] == oslo))  # Day 16
    s.add(Or(E[16] == oslo, E[17] == oslo))  # Day 17
    
    reykjavik = city_dict['Reykjavik']
    s.add(Or([Or(E[d-1] == reykjavik, E[d] == reykjavik) for d in range(9, 14)]))  # Days 9-13
    
    munich = city_dict['Munich']
    for d in range(13, 17):  # Days 13-16
        s.add(Or(E[d-1] == munich, E[d] == munich))
    
    frankfurt = city_dict['Frankfurt']
    for d in range(17, 21):  # Days 17-20
        s.add(Or(E[d-1] == frankfurt, E[d] == frankfurt))
    
    # Solve and output
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for d in range(1, 21):
            c_val = model[E[d]]
            city_name = [name for name, const in city_dict.items() if model.evaluate(const) == c_val][0]
            itinerary.append({"day_range": f"Day {d}", "place": city_name})
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()