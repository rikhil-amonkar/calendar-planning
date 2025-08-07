from z3 import *

def solve_itinerary():
    # Cities
    Prague, Berlin, Tallinn, Stockholm = 'Prague', 'Berlin', 'Tallinn', 'Stockholm'
    cities = [Prague, Berlin, Tallinn, Stockholm]
    
    # Days are 1..12
    days = list(range(1, 13))
    
    # Create solver
    s = Solver()
    
    # Variables: for each day, which cities are we in?
    day_city = {}
    for day in days:
        for city in cities:
            day_city[(day, city)] = Bool(f"day_{day}_{city}")
    
    # Constraints
    
    # 1. Each day must be in exactly one city (no travel days counted twice)
    for day in days:
        # Exactly one city per day
        s.add(ExactlyOne([day_city[(day, city)] for city in cities]))
    
    # 2. Total days per city constraints
    # Prague: 2 days
    s.add(Sum([If(day_city[(day, Prague)], 1, 0) for day in days]) == 2)
    # Berlin: 3 days (including conference days)
    s.add(Sum([If(day_city[(day, Berlin)], 1, 0) for day in days]) == 3)
    # Tallinn: 5 days (including relatives visit)
    s.add(Sum([If(day_city[(day, Tallinn)], 1, 0) for day in days]) == 5)
    # Stockholm: 5 days
    s.add(Sum([If(day_city[(day, Stockholm)], 1, 0) for day in days]) == 5)
    
    # 3. Conference in Berlin on days 6 and 8
    s.add(day_city[(6, Berlin)])
    s.add(day_city[(8, Berlin)])
    
    # 4. Relatives in Tallinn between day 8 and day 12
    # So days 9-12 must be in Tallinn
    for day in [9, 10, 11, 12]:
        s.add(day_city[(day, Tallinn)])
    
    # 5. Travel constraints: if consecutive days are in different cities, 
    # there must be a direct flight between them
    direct_flights = {
        (Berlin, Tallinn),
        (Tallinn, Berlin),
        (Prague, Tallinn),
        (Tallinn, Prague),
        (Stockholm, Tallinn),
        (Tallinn, Stockholm),
        (Prague, Stockholm),
        (Stockholm, Prague),
        (Stockholm, Berlin),
        (Berlin, Stockholm)
    }
    
    for day in days[:-1]:
        next_day = day + 1
        for c1 in cities:
            for c2 in cities:
                if c1 != c2:
                    # If we're in c1 on day and c2 on next_day, must have direct flight
                    s.add(Implies(
                        And(day_city[(day, c1)], day_city[(next_day, c2)]),
                        Or([And(c1 == a, c2 == b) for (a, b) in direct_flights])
                    ))
    
    # Check if satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in days:
            for city in cities:
                if m.evaluate(day_city[(day, city)]):
                    itinerary.append({"day": day, "place": [city]})
                    break
        
        # Verify all constraints are met
        # Count days per city
        counts = {city: 0 for city in cities}
        for entry in itinerary:
            counts[entry['place'][0]] += 1
        
        assert counts[Prague] == 2
        assert counts[Berlin] == 3
        assert counts[Tallinn] == 5
        assert counts[Stockholm] == 5
        
        # Verify conference days
        assert itinerary[5]['place'][0] == Berlin  # Day 6
        assert itinerary[7]['place'][0] == Berlin  # Day 8
        
        # Verify relatives visit
        for day in [9, 10, 11, 12]:
            assert itinerary[day-1]['place'][0] == Tallinn
        
        # Verify direct flights between consecutive cities
        for i in range(len(itinerary)-1):
            current = itinerary[i]['place'][0]
            next_c = itinerary[i+1]['place'][0]
            if current != next_c:
                assert (current, next_c) in direct_flights
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))