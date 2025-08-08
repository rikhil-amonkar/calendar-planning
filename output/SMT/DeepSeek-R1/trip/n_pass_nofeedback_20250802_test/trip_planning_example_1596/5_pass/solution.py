from z3 import Solver, Bool, Or, And, Not, Sum, If, sat, is_true
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
    
    connected_pairs = set()
    for A, B in direct_flights:
        connected_pairs.add(tuple(sorted([A, B])))
    
    s = Solver()
    in_city = {}
    for city in cities:
        in_city[city] = [Bool(f"in_{city}_{day}") for day in range(32)]
    
    for day in range(32):
        day_vars = [in_city[city][day] for city in cities]
        total_cities = Sum([If(v, 1, 0) for v in day_vars])
        s.add(Or(total_cities == 1, total_cities == 2))
        
        # Flight constraint: if two cities, they must be connected
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                city1 = cities[i]
                city2 = cities[j]
                if (city1, city2) not in connected_pairs:
                    s.add(Not(And(in_city[city1][day], in_city[city2][day])))
    
    for day in range(31):
        common = Or([And(in_city[city][day], in_city[city][day+1]) for city in cities])
        s.add(common)
    
    for city in cities:
        total_days = Sum([If(in_city[city][d], 1, 0) for d in range(32)])
        s.add(total_days == durations[city])
    
    # Event constraints
    for day in [8, 9, 10, 11, 12]:  # Days 9-13 (0-indexed days 8-12)
        s.add(in_city['Budapest'][day])
    for day in [24, 25, 26, 27, 28]:  # Days 25-29 (0-indexed days 24-28)
        s.add(in_city['Warsaw'][day])
    for day in [17, 18, 19]:  # Days 18-20 (0-indexed days 17-19)
        s.add(in_city['Munich'][day])
    s.add(Or(in_city['Stockholm'][16], in_city['Stockholm'][17]))  # Day 17 or 18
    s.add(Or([in_city['Edinburgh'][d] for d in range(5)]))  # At least one of first 5 days
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        
        # Validate durations
        for city in cities:
            count = sum(1 for day in range(32) if is_true(m[in_city[city][day]]))
            assert count == durations[city], f"Duration failed: {city} has {count} days (expected {durations[city]})"
        
        # Validate event constraints
        for day in [8, 9, 10, 11, 12]:
            assert is_true(m[in_city['Budapest'][day]]), f"Budapest missing on day {day+1}"
        for day in [24, 25, 26, 27, 28]:
            assert is_true(m[in_city['Warsaw'][day]]), f"Warsaw missing on day {day+1}"
        for day in [17, 18, 19]:
            assert is_true(m[in_city['Munich'][day]]), f"Munich missing on day {day+1}"
        assert is_true(m[Or(in_city['Stockholm'][16], in_city['Stockholm'][17])]), "Stockholm missing on day 17 or 18"
        assert any(is_true(m[in_city['Edinburgh'][d]]) for d in range(5)), "Edinburgh missing in first 5 days"
        
        # Validate flight days
        for day in range(32):
            present_cities = [city for city in cities if is_true(m[in_city[city][day]])]
            if len(present_cities) == 2:
                city1, city2 = sorted(present_cities)
                assert (city1, city2) in connected_pairs, f"Invalid flight: {city1} and {city2} on day {day+1}"
        
        # Build itinerary
        for day in range(32):
            present_cities = [city for city in cities if is_true(m[in_city[city][day]])]
            if len(present_cities) == 1:
                place = present_cities[0]
            else:
                place = sorted(present_cities)
            itinerary.append({"day": day+1, "place": place})
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()