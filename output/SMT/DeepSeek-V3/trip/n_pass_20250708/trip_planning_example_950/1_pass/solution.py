import json
from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Rome', 'Mykonos', 'Riga', 'Munich', 'Bucharest', 'Nice', 'Krakow']
    
    # Direct flights as a set of tuples
    direct_flights = {
        ('Nice', 'Riga'), ('Bucharest', 'Munich'), ('Mykonos', 'Munich'), 
        ('Riga', 'Bucharest'), ('Rome', 'Nice'), ('Rome', 'Munich'), 
        ('Mykonos', 'Nice'), ('Rome', 'Mykonos'), ('Munich', 'Krakow'), 
        ('Rome', 'Bucharest'), ('Nice', 'Munich'), ('Riga', 'Munich'), 
        ('Rome', 'Riga')
    }
    # Make flights bidirectional
    flights = set()
    for a, b in direct_flights:
        flights.add((a, b))
        flights.add((b, a))
    
    # Total days
    days = 17
    
    # Create Z3 variables: day[i] is the city for day i+1 (1-based)
    day = [Int(f'day_{i}') for i in range(1, days + 1)]
    
    # Create a mapping from city name to integer
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    s = Solver()
    
    # Each day's assignment must be a valid city (0 to 6)
    for d in day:
        s.add(And(d >= 0, d < len(cities)))
    
    # Fixed constraints:
    # Days 1-4: conference in Rome (so days 1, 2, 3, 4 are Rome)
    for i in [0, 1, 2, 3]:  # Days 1-4
        s.add(day[i] == city_to_int['Rome'])
    
    # Days 16-17: Krakow
    s.add(day[15] == city_to_int['Krakow'])  # Day 16
    s.add(day[16] == city_to_int['Krakow'])  # Day 17
    
    # Flight constraints: consecutive days must be same city or connected by flight
    for i in range(days - 1):
        current_city = day[i]
        next_city = day[i + 1]
        # Either same city or connected by flight
        same_city = current_city == next_city
        flight_possible = Or([And(current_city == city_to_int[a], next_city == city_to_int[b]) for (a, b) in flights])
        s.add(Or(same_city, flight_possible))
    
    # Total days per city constraints
    # Rome: 4 days (including days 1-4)
    rome_days = Sum([If(day[i] == city_to_int['Rome'], 1, 0) for i in range(days)])
    s.add(rome_days == 4)
    
    # Mykonos: 3 days
    mykonos_days = Sum([If(day[i] == city_to_int['Mykonos'], 1, 0) for i in range(days)])
    s.add(mykonos_days == 3)
    # Wedding in Mykonos between day 4 and 6: so at least one of days 5 or 6 is Mykonos.
    s.add(Or(day[4] == city_to_int['Mykonos'], day[5] == city_to_int['Mykonos']))
    
    # Riga: 3 days
    riga_days = Sum([If(day[i] == city_to_int['Riga'], 1, 0) for i in range(days)])
    s.add(riga_days == 3)
    
    # Munich: 4 days
    munich_days = Sum([If(day[i] == city_to_int['Munich'], 1, 0) for i in range(days)])
    s.add(munich_days == 4)
    
    # Bucharest: 4 days
    bucharest_days = Sum([If(day[i] == city_to_int['Bucharest'], 1, 0) for i in range(days)])
    s.add(bucharest_days == 4)
    
    # Nice: 3 days
    nice_days = Sum([If(day[i] == city_to_int['Nice'], 1, 0) for i in range(days)])
    s.add(nice_days == 3)
    
    # Krakow: 2 days (already fixed days 16-17)
    krakow_days = Sum([If(day[i] == city_to_int['Krakow'], 1, 0) for i in range(days)])
    s.add(krakow_days == 2)
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        # Extract the day assignments
        schedule = []
        for i in range(days):
            city_idx = model.evaluate(day[i]).as_long()
            schedule.append(int_to_city[city_idx])
        
        # Generate the itinerary in the required JSON format
        itinerary = []
        current_place = schedule[0]
        start_day = 1
        
        for i in range(1, days):
            if schedule[i] == current_place:
                continue
            else:
                end_day = i
                if start_day == end_day:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_place})
                # Add flight day entries
                itinerary.append({"day_range": f"Day {end_day}", "place": current_place})
                itinerary.append({"day_range": f"Day {end_day}", "place": schedule[i]})
                current_place = schedule[i]
                start_day = end_day + 1
        
        # Add the last segment
        if start_day <= days:
            if start_day == days:
                itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{days}", "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))