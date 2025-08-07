from z3 import *

def solve_itinerary():
    # Cities and indices
    cities = ['Krakow', 'Frankfurt', 'Oslo', 'Dubrovnik', 'Naples']
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    Krakow, Frankfurt, Oslo, Dubrovnik, Naples = range(5)
    
    total_days = 18
    s = Solver()
    
    # Variables: city each day (1-18)
    day_place = [Int(f'day_{d}_place') for d in range(1, total_days+1)]
    for d in range(total_days):
        s.add(day_place[d] >= 0, day_place[d] <= 4)
    
    # Flight connections (bidirectional)
    direct_flights = [
        (Dubrovnik, Oslo),
        (Frankfurt, Krakow),
        (Frankfurt, Oslo),
        (Dubrovnik, Frankfurt),
        (Krakow, Oslo),
        (Naples, Oslo),
        (Naples, Dubrovnik),
        (Naples, Frankfurt)
    ]
    all_flights = direct_flights + [(b,a) for (a,b) in direct_flights]
    
    # Flight constraints
    for d in range(total_days-1):
        current = day_place[d]
        next_ = day_place[d+1]
        s.add(Or(current == next_, Or([And(current == a, next_ == b) for (a,b) in all_flights])))
    
    # Count days in each city (including flight days)
    def days_in(city_idx):
        return Sum([If(day_place[d] == city_idx, 1, 0) for d in range(total_days)])
    
    s.add(days_in(Krakow) == 5)
    s.add(days_in(Frankfurt) == 4)
    s.add(days_in(Oslo) == 3)
    s.add(days_in(Dubrovnik) == 5)
    s.add(days_in(Naples) == 5)
    
    # Oslo between days 16-18
    s.add(Or([day_place[d] == Oslo for d in range(15,18)]))
    
    # Dubrovnik between days 5-9
    s.add(Or([day_place[d] == Dubrovnik for d in range(4,9)]))
    
    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for d in range(total_days):
            city_idx = m.evaluate(day_place[d]).as_long()
            itinerary.append({'day': d+1, 'place': cities[city_idx]})
        
        # Verification
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry['place']] += 1
        
        assert city_days['Krakow'] == 5
        assert city_days['Frankfurt'] == 4
        assert city_days['Oslo'] == 3
        assert city_days['Dubrovnik'] == 5
        assert city_days['Naples'] == 5
        
        # Check Oslo days 16-18
        oslo_days = [entry['day'] for entry in itinerary if entry['place'] == 'Oslo']
        assert any(16 <= day <= 18 for day in oslo_days)
        
        # Check Dubrovnik days 5-9
        dubrovnik_days = [entry['day'] for entry in itinerary if entry['place'] == 'Dubrovnik']
        assert any(5 <= day <= 9 for day in dubrovnik_days)
        
        # Check flight connections
        for i in range(len(itinerary)-1):
            current = itinerary[i]['place']
            next_ = itinerary[i+1]['place']
            if current != next_:
                assert (city_to_idx[current], city_to_idx[next_]) in all_flights
        
        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))
else:
    print("No solution found")