from z3 import *
import json

def main():
    # Define the list of cities
    cities = ['Oslo', 'Reykjavik', 'Stockholm', 'Munich', 'Frankfurt', 'Barcelona', 'Bucharest', 'Split']
    
    # Create an enumeration for the cities
    CitySort, city_consts = EnumSort('City', cities)
    city_dict = {name: const for name, const in zip(cities, city_consts)}
    
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
    E = [Const('E%d' % i, CitySort) for i in range(21)]
    
    s = Solver()
    
    # Flight constraints for each day from 1 to 20
    for d in range(1, 21):
        prev_city = E[d-1]
        curr_city = E[d]
        # If the city changes, ensure the flight is allowed
        flight_cond = Or([And(prev_city == a, curr_city == b) for (a, b) in allowed_pairs])
        s.add(If(prev_city != curr_city, flight_cond, True))
    
    # Total days per city: count for each day i (from 1 to 20) and each city
    total_days = {city: 0 for city in cities}
    for city in cities:
        c = city_dict[city]
        count = 0
        for d in range(1, 21):
            # Day d: from E_{d-1} to E_d
            count += If(Or(E[d-1] == c, E[d] == c), 1, 0)
        s.add(count == {
            'Oslo': 2,
            'Reykjavik': 5,
            'Stockholm': 4,
            'Munich': 4,
            'Frankfurt': 4,
            'Barcelona': 3,
            'Bucharest': 2,
            'Split': 3
        }[city])
    
    # Specific event constraints
    oslo = city_dict['Oslo']
    # For day16: either E15 or E16 must be Oslo
    s.add(Or(E[15] == oslo, E[16] == oslo))
    # For day17: either E16 or E17 must be Oslo
    s.add(Or(E[16] == oslo, E[17] == oslo))
    
    reykjavik = city_dict['Reykjavik']
    # At least one day in [9,13] must be in Reykjavik
    s.add(Or([Or(E[d-1] == reykjavik, E[d] == reykjavik) for d in range(9, 14)]))
    
    munich = city_dict['Munich']
    # For each day in [13,16]: must be in Munich
    for d in range(13, 17):
        s.add(Or(E[d-1] == munich, E[d] == munich))
    
    frankfurt = city_dict['Frankfurt']
    # For each day in [17,20]: must be in Frankfurt
    for d in range(17, 21):
        s.add(Or(E[d-1] == frankfurt, E[d] == frankfurt))
    
    # Solve the problem
    if s.check() == sat:
        model = s.model()
        itinerary = []
        # We output from day1 to day20: the city at the end of the day (E1 to E20)
        for d in range(1, 21):
            c_val = model[E[d]]
            place = None
            for city in cities:
                if model.evaluate(city_dict[city]) == c_val:
                    place = city
                    break
            itinerary.append({"day": d, "place": place})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()