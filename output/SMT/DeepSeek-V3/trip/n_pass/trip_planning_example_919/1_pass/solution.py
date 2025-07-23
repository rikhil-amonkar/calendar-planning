from z3 import *

def solve_itinerary():
    # Cities and their codes
    cities = {
        'Vienna': 0,
        'Milan': 1,
        'Rome': 2,
        'Riga': 3,
        'Lisbon': 4,
        'Vilnius': 5,
        'Oslo': 6
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 5, 4, 3, 2, 6],  # Vienna
        1: [0, 3, 6, 4, 5],       # Milan
        2: [6, 3, 4, 0],          # Rome
        3: [6, 0, 1, 5, 4, 2],    # Riga
        4: [0, 6, 2, 1, 3],       # Lisbon
        5: [0, 6, 3, 1],          # Vilnius
        6: [3, 2, 4, 1, 0, 5]     # Oslo
    }
    
    s = Solver()
    
    # For each day, the person is in one or two cities (if it's a travel day)
    # So for each day, we have a list of cities that are visited.
    # But in Z3, it's easier to model this as a list of possible cities per day.
    # So for each day, we'll have a variable indicating the city, and possibly a travel city.
    # Alternatively, for each day and city, a Bool indicating whether the person is in that city.
    
    day_city = [[Bool(f"day_{day}_city_{city}") for city in cities.values()] for day in range(1, 16)]
    
    # Each day, the person is in at least one city, at most two.
    for day in range(15):
        current_day = day
        s.add(Or(day_city[current_day]))  # at least one city per day
        # At most two cities per day
        for i in range(7):
            for j in range(i+1, 7):
                for k in range(j+1, 7):
                    s.add(Not(And(day_city[current_day][i], day_city[current_day][j], day_city[current_day][k])))
    
    # Flight constraints: if the person is in city A on day d and city B on day d+1, and A != B, then:
    # day d must include city A and city B (travel day), or day d+1 must include city B and city A (but this may not make sense).
    # Alternatively, if day d is in city A and day d+1 is in city B, then either:
    # - day d is in both A and B (travel day from A to B), or
    # - day d+1 is in both A and B (travel day from B to A), but this is not possible.
    # So the correct constraint is that if day d is in A and day d+1 is in B, then either A == B or day d is in both A and B.
    for day in range(14):
        current_day = day
        next_day = day + 1
        for c1 in cities.values():
            for c2 in cities.values():
                if c1 != c2:
                    s.add(Implies(
                        And(day_city[current_day][c1], day_city[next_day][c2]),
                        And(day_city[current_day][c2], c2 in direct_flights[c1])
                    ))
    
    # Fixed days:
    # Day 1 and 4 must be in Vienna (conference)
    s.add(day_city[0][cities['Vienna']])  # day 1
    s.add(day_city[3][cities['Vienna']])  # day 4
    
    # Relatives in Lisbon between day 11-13 (days 11,12,13)
    for day in [10, 11, 12]:
        s.add(day_city[day][cities['Lisbon']])
    
    # Friend in Oslo between day 13-15 (days 13,14,15)
    for day in [12, 13, 14]:
        s.add(day_city[day][cities['Oslo']])
    
    # Total days per city:
    city_days = {
        'Vienna': 4,
        'Milan': 2,
        'Rome': 3,
        'Riga': 2,
        'Lisbon': 3,
        'Vilnius': 4,
        'Oslo': 3
    }
    
    for city, total in city_days.items():
        city_code = cities[city]
        s.add(Sum([If(day_city[day][city_code], 1, 0) for day in range(15)]) == total)
    
    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(15):
            current_day = day + 1
            places = []
            for city_code in cities.values():
                if is_true(m.evaluate(day_city[day][city_code])):
                    places.append(city_names[city_code])
            for place in places:
                itinerary.append({'day': current_day, 'place': place})
        
        # Group by day
        grouped = {}
        for entry in itinerary:
            day = entry['day']
            place = entry['place']
            if day not in grouped:
                grouped[day] = place
            else:
                grouped[day] += f", {place}"
        
        itinerary_list = [{'day': day, 'place': place} for day, place in sorted(grouped.items())]
        return {'itinerary': itinerary_list}
    else:
        return {"error": "No solution found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))