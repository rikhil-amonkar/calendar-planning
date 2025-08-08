from z3 import *
import json

def main():
    # Define the list of cities
    cities_list = ['Oslo', 'Reykjavik', 'Stockholm', 'Munich', 'Frankfurt', 'Barcelona', 'Bucharest', 'Split']
    City, city_enums = EnumSort('City', cities_list)
    city_dict = {name: getattr(city_enums, name) for name in cities_list}
    
    # Define direct flight pairs as strings
    direct_flight_pairs = [
        ("Reykjavik", "Munich"),
        ("Munich", "Frankfurt"),
        ("Split", "Oslo"),
        ("Reykjavik", "Oslo"),
        ("Bucharest", "Munich"),
        ("Oslo", "Frankfurt"),
        ("Bucharest", "Barcelona"),
        ("Barcelona", "Frankfurt"),
        ("Reykjavik", "Frankfurt"),
        ("Barcelona", "Stockholm"),
        ("Barcelona", "Reykjavik"),
        ("Stockholm", "Reykjavik"),
        ("Barcelona", "Split"),
        ("Bucharest", "Oslo"),
        ("Bucharest", "Frankfurt"),
        ("Split", "Stockholm"),
        ("Barcelona", "Oslo"),
        ("Stockholm", "Munich"),
        ("Stockholm", "Oslo"),
        ("Split", "Frankfurt"),
        ("Barcelona", "Munich"),
        ("Stockholm", "Frankfurt"),
        ("Munich", "Oslo"),
        ("Split", "Munich")
    ]
    
    # Build the set of allowed flight pairs (as Z3 constants)
    allowed_pairs = set()
    for (a, b) in direct_flight_pairs:
        a_const = city_dict[a]
        b_const = city_dict[b]
        allowed_pairs.add((a_const, b_const))
        allowed_pairs.add((b_const, a_const))
    
    # Define variables: E0 to E20 (E0 is the starting city at day0, E1 is end of day1, ..., E20 end of day20)
    E = [Const('E%d' % i, City) for i in range(21)]
    
    s = Solver()
    
    # Flight constraints for each day from 1 to 20
    for d in range(1, 21):
        prev_city = E[d-1]
        curr_city = E[d]
        # If the city changes, ensure the flight is allowed
        flight_cond = Or([And(prev_city == a, curr_city == b) for (a, b) in allowed_pairs])
        s.add(If(prev_city != curr_city, flight_cond, True))
    
    # Total days per city
    total_days = {name: 0 for name in cities_list}
    for d in range(1, 21):
        for name in cities_list:
            c = city_dict[name]
            total_days[name] += If(Or(E[d-1] == c, E[d] == c), 1, 0)
    
    # Add constraints for total days
    s.add(total_days['Oslo'] == 2)
    s.add(total_days['Reykjavik'] == 5)
    s.add(total_days['Stockholm'] == 4)
    s.add(total_days['Munich'] == 4)
    s.add(total_days['Frankfurt'] == 4)
    s.add(total_days['Barcelona'] == 3)
    s.add(total_days['Bucharest'] == 2)
    s.add(total_days['Split'] == 3)
    
    # Specific event constraints
    oslo = city_dict['Oslo']
    s.add(Or(E[15] == oslo, E[16] == oslo))  # Day 16: presence in Oslo
    s.add(Or(E[16] == oslo, E[17] == oslo))  # Day 17: presence in Oslo
    
    reykjavik = city_dict['Reykjavik']
    s.add(Or([Or(E[d-1] == reykjavik, E[d] == reykjavik) for d in range(9, 14)]))  # Days 9-13
    
    munich = city_dict['Munich']
    s.add(Or([Or(E[d-1] == munich, E[d] == munich) for d in range(13, 17)]))  # Days 13-16
    
    frankfurt = city_dict['Frankfurt']
    s.add(Or([Or(E[d-1] == frankfurt, E[d] == frankfurt) for d in range(17, 21)]))  # Days 17-20
    
    # Solve the problem
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for d in range(1, 21):
            c_val = model[E[d]]
            place = None
            for name in cities_list:
                if model.eval(city_dict[name]).eq(c_val):
                    place = name
                    break
            if place is None:
                place = "Unknown"
            itinerary.append({"day": d, "place": place})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()