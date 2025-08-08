from z3 import *

def solve_itinerary():
    # Cities
    Valencia, Athens, Naples, Zurich = 0, 1, 2, 3
    cities = ['Valencia', 'Athens', 'Naples', 'Zurich']
    
    # Direct flights: adjacency list
    direct_flights = {
        Valencia: [Naples, Athens, Zurich],
        Athens: [Valencia, Naples, Zurich],
        Naples: [Valencia, Athens, Zurich],
        Zurich: [Naples, Athens, Valencia]
    }
    
    # Create Z3 variables for each day
    day_city = [Int(f'day_{i}_city') for i in range(1, 21)]
    
    s = Solver()
    
    # Each day must be assigned to a valid city
    for day in day_city:
        s.add(Or([day == c for c in [Valencia, Athens, Naples, Zurich]]))
    
    # Must be in Athens days 1-6
    for i in range(6):
        s.add(day_city[i] == Athens)
    
    # Must be in Naples days 16-20
    for i in range(15, 20):
        s.add(day_city[i] == Naples)
    
    # Total days per city
    total_valencia = sum([If(day_city[i] == Valencia, 1, 0) for i in range(20)])
    total_athens = sum([If(day_city[i] == Athens, 1, 0) for i in range(20)])
    total_naples = sum([If(day_city[i] == Naples, 1, 0) for i in range(20)])
    total_zurich = sum([If(day_city[i] == Zurich, 1, 0) for i in range(20)])
    
    s.add(total_valencia == 6)
    s.add(total_athens == 6)
    s.add(total_naples == 5)
    s.add(total_zurich == 6)
    
    # Flight transitions must use direct flights
    for i in range(19):
        city_today = day_city[i]
        city_tomorrow = day_city[i+1]
        s.add(Implies(city_today != city_tomorrow,
                     Or([And(city_today == a, city_tomorrow == b)
                         for a in direct_flights
                         for b in direct_flights[a] if a != b])))
    
    # Check if solution exists
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(1, 21):
            city_idx = m.evaluate(day_city[day-1]).as_long()
            city = cities[city_idx]
            itinerary.append({"day": day, "place": city})
        
        # Verify all constraints
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place']] += 1
        
        assert counts['Valencia'] == 6
        assert counts['Athens'] == 6
        assert counts['Naples'] == 5
        assert counts['Zurich'] == 6
        
        # Verify Athens days 1-6
        for day in range(1, 7):
            assert itinerary[day-1]['place'] == 'Athens'
        
        # Verify Naples days 16-20
        for day in range(16, 21):
            assert itinerary[day-1]['place'] == 'Naples'
        
        # Verify flight transitions
        for i in range(19):
            from_city = itinerary[i]['place']
            to_city = itinerary[i+1]['place']
            if from_city != to_city:
                from_idx = cities.index(from_city)
                to_idx = cities.index(to_city)
                assert to_idx in direct_flights[from_idx], f"No direct flight from {from_city} to {to_city}"
        
        return {'itinerary': itinerary}
    else:
        print("No valid itinerary found")
        return None

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))