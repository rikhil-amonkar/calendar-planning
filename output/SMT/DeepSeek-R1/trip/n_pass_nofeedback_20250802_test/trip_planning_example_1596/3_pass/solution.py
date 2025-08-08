from z3 import Solver, Bool, Or, And, Not, Sum, If, sat
import json

def main():
    cities = ['Bucharest', 'Krakow', 'Munich', 'Barcelona', 'Warsaw', 'Budapest', 'Stockholm', 'Riga', 'Edinburgh', 'Vienna']
    durations = {
        'Bucharest': 2,
        'Krakow': 4,
        'Munich': 3,
        'Barcelona': 5,
        'Warsaw': 5,
        'Budapest': 5,
        'Stockholm': 2,
        'Riga': 5,
        'Edinburgh': 5,
        'Vienna': 5
    }
    
    flight_str = "Budapest and Munich, Bucharest and Riga, Munich and Krakow, Munich and Warsaw, Munich and Bucharest, Edinburgh and Stockholm, Barcelona and Warsaw, Edinburgh and Krakow, Barcelona and Munich, Stockholm and Krakow, Budapest and Vienna, Barcelona and Stockholm, Stockholm and Munich, Edinburgh and Budapest, Barcelona and Riga, Edinburgh and Barcelona, Vienna and Riga, Barcelona and Budapest, Bucharest and Warsaw, Vienna and Krakow, Edinburgh and Munich, Barcelona and Bucharest, Edinburgh and Riga, Vienna and Stockholm, Warsaw and Krakow, Barcelona and Krakow, from Riga to Munich, Vienna and Bucharest, Budapest and Warsaw, Vienna and Warsaw, Barcelona and Vienna, Budapest and Bucharest, Vienna and Munich, Riga and Warsaw, Stockholm and Riga, Stockholm and Warsaw"
    flight_str = flight_str.replace("from ", "").replace(" to ", " and ")
    flights = flight_str.split(", ")
    direct_flights = set()
    for flight in flights:
        parts = flight.split(" and ")
        if len(parts) == 2:
            A, B = parts
            direct_flights.add((A, B))
            direct_flights.add((B, A))
    
    # Create set of canonical flight pairs (sorted order)
    connected_pairs = {tuple(sorted((A, B))) for (A, B) in direct_flights}
    
    s = Solver()
    in_city = {}
    for city in cities:
        in_city[city] = [Bool(f"in_{city}_{day}") for day in range(1, 33)]
    
    for day in range(32):
        day_vars = [in_city[city][day] for city in cities]
        total_cities = Sum([If(v, 1, 0) for v in day_vars])
        option1 = (total_cities == 1)
        option2 = (total_cities == 2)
        
        # Positive flight constraint: if two cities, they must be connected
        if connected_pairs:
            two_cities_constraint = Or([
                And(in_city[pair[0]][day], in_city[pair[1]][day]) 
                for pair in connected_pairs
            ])
        else:
            two_cities_constraint = False
        
        s.add(Or(option1, And(option2, two_cities_constraint)))
    
    for day in range(31):
        common = Or([And(in_city[city][day], in_city[city][day+1]) for city in cities])
        s.add(common)
    
    for city in cities:
        total_days = Sum([If(in_city[city][d], 1, 0) for d in range(32)])
        s.add(total_days == durations[city])
    
    # Event constraints
    for day_index in [8, 9, 10, 11, 12]:  # Days 9-13
        s.add(in_city['Budapest'][day_index])
    for day_index in [24, 25, 26, 27, 28]:  # Days 25-29
        s.add(in_city['Warsaw'][day_index])
    for day_index in [17, 18, 19]:  # Days 18-20
        s.add(in_city['Munich'][day_index])
    s.add(Or(in_city['Stockholm'][16], in_city['Stockholm'][17]))  # Day 17 or 18
    s.add(Or([in_city['Edinburgh'][d] for d in range(5)]))  # First 5 days
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        # Validate durations
        for city in cities:
            count = sum(1 for day in range(32) if m.evaluate(in_city[city][day]))
            assert count == durations[city], f"{city} has {count} days, expected {durations[city]}"
        
        # Build itinerary
        for day_index in range(32):
            present_cities = []
            for city in cities:
                if m.evaluate(in_city[city][day_index]):
                    present_cities.append(city)
            if len(present_cities) == 1:
                place = present_cities[0]
            else:
                present_cities.sort()
                place = present_cities
            itinerary.append({"day": day_index+1, "place": place})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()