from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Berlin': 5,
        'Split': 3,
        'Bucharest': 3,
        'Riga': 5,
        'Lisbon': 3,
        'Tallinn': 4,
        'Lyon': 5
    }
    city_list = list(cities.keys())
    
    # Direct flights as a set of tuples
    direct_flights = {
        ('Lisbon', 'Bucharest'),
        ('Berlin', 'Lisbon'),
        ('Bucharest', 'Riga'),
        ('Berlin', 'Riga'),
        ('Split', 'Lyon'),
        ('Lisbon', 'Riga'),
        ('Riga', 'Tallinn'),
        ('Berlin', 'Split'),
        ('Lyon', 'Lisbon'),
        ('Berlin', 'Tallinn'),
        ('Lyon', 'Bucharest')
    }
    # Make sure flights are bidirectional
    flights = set()
    for (a, b) in direct_flights:
        flights.add((a, b))
        flights.add((b, a))
    
    # Total days
    total_days = 22
    
    # Create a solver instance
    s = Solver()
    
    # Create variables: for each day and city, a boolean indicating presence
    presence = [[Bool(f"day_{day}_in_{city}") for city in city_list] for day in range(1, total_days + 1)]
    
    # Constraints
    
    # 1. Each day must be in at least one city (but possibly more due to flights)
    for day in range(total_days):
        s.add(Or([presence[day][i] for i in range(len(city_list))]))
    
    # 2. Fixed days:
    # Berlin from day 1 to 5 (1-based)
    for day in range(0, 5):
        s.add(presence[day][city_list.index('Berlin')])
    
    # Bucharest between day 13-15 (1-based, days 13,14,15 are indices 12,13,14)
    for day in [12, 13, 14]:
        s.add(presence[day][city_list.index('Bucharest')])
    
    # Lyon between day 7-11 (1-based, days 7-11 are indices 6-10)
    for day in range(6, 11):
        s.add(presence[day][city_list.index('Lyon')])
    
    # 3. Total days per city must match requirements
    for city_idx, city in enumerate(city_list):
        total = 0
        for day in range(total_days):
            total += If(presence[day][city_idx], 1, 0)
        s.add(total == cities[city])
    
    # 4. Transition constraints: if you're in city A on day d and city B on day d+1, then (A,B) must be in flights or A == B
    for day in range(total_days - 1):
        current_day_presence = presence[day]
        next_day_presence = presence[day + 1]
        # For each pair of cities (i, j) where i != j, if day is in i and day+1 is in j, then (i,j) must be in flights
        for i in range(len(city_list)):
            for j in range(len(city_list)):
                if i != j:
                    # If day is in i and day+1 is in j, then (i,j) must be in flights
                    s.add(Implies(And(current_day_presence[i], next_day_presence[j]), 
                                  (city_list[i], city_list[j]) in flights))
    
    # Solve the problem
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(total_days):
            day_num = day + 1
            current_cities = []
            for city_idx in range(len(city_list)):
                if model.evaluate(presence[day][city_idx]):
                    current_cities.append(city_list[city_idx])
            # On flight days, you're in multiple cities. We'll pick the arrival city for the itinerary.
            # But the JSON requires each day to have one place. So we need to choose one.
            # According to the problem's note, the flight day is counted for both cities.
            # So for the itinerary, we can choose the arrival city (the one that's new compared to the previous day).
            # But since the JSON output should list the place for each day, we'll pick the first city in the list for simplicity.
            # Alternatively, we can pick the city that's different from the previous day's city (if any).
            # Here, we'll just pick the first city in current_cities for the itinerary.
            place = current_cities[0] if current_cities else None
            itinerary.append({"day": day_num, "place": place})
        
        # Verify the itinerary meets all constraints
        # (This step is optional but helpful for debugging)
        city_days = {city: 0 for city in city_list}
        for entry in itinerary:
            city_days[entry['place']] += 1
        
        for city in city_list:
            assert city_days[city] == cities[city], f"City {city} has {city_days[city]} days instead of {cities[city]}"
        
        # Check fixed days
        for day in range(1, 6):
            assert itinerary[day - 1]['place'] == 'Berlin', f"Day {day} should be Berlin"
        for day in [13, 14, 15]:
            assert itinerary[day - 1]['place'] == 'Bucharest', f"Day {day} should be Bucharest"
        for day in range(7, 12):
            assert itinerary[day - 1]['place'] == 'Lyon', f"Day {day} should be Lyon"
        
        # Check transitions
        for day in range(1, total_days):
            prev_place = itinerary[day - 1]['place']
            curr_place = itinerary[day]['place']
            if prev_place != curr_place:
                assert (prev_place, curr_place) in flights, f"No flight from {prev_place} to {curr_place} on day {day}"
        
        # Format the output
        output = {
            "itinerary": itinerary
        }
        return output
    else:
        return {"error": "No solution found"}

# Generate the solution
solution = solve_itinerary()
print(json.dumps(solution, indent=2))