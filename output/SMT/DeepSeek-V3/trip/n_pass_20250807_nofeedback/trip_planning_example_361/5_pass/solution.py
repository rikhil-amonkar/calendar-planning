from z3 import *
import json

def solve_itinerary():
    s = Solver()

    Cities = {'Paris': 0, 'Madrid': 1, 'Bucharest': 2, 'Seville': 3}
    cities = ['Paris', 'Madrid', 'Bucharest', 'Seville']
    direct_flights = {
        Cities['Paris']: [Cities['Bucharest'], Cities['Seville']],
        Cities['Madrid']: [Cities['Bucharest'], Cities['Paris'], Cities['Seville']],
        Cities['Bucharest']: [Cities['Paris'], Cities['Madrid']],
        Cities['Seville']: [Cities['Paris'], Cities['Madrid']]
    }

    # For each day, the cities the traveler is in (up to 2)
    day_city = [[Bool(f"day_{day}_city_{city}") for city in range(4)] for day in range(15)]

    # Constraints:

    # 1. Days 1-7 (0-based 0-6) must be in Madrid.
    for day in range(7):
        s.add(day_city[day][Cities['Madrid']] == True)
        for city in [Cities['Paris'], Cities['Bucharest'], Cities['Seville']]:
            s.add(day_city[day][city] == False)

    # 2. Bucharest must be visited on days 14 and 15 (0-based 13 and 14)
    s.add(day_city[13][Cities['Bucharest']] == True)
    s.add(day_city[14][Cities['Bucharest']] == True)
    # On day 15 (0-based 14), only Bucharest.
    for city in [Cities['Paris'], Cities['Madrid'], Cities['Seville']]:
        s.add(day_city[14][city] == False)

    # 3. Total days per city:
    s.add(Sum([If(day_city[d][Cities['Paris']], 1, 0) for d in range(15)]) == 6)
    s.add(Sum([If(day_city[d][Cities['Madrid']], 1, 0) for d in range(15)]) == 7)
    s.add(Sum([If(day_city[d][Cities['Bucharest']], 1, 0) for d in range(15)]) == 2)
    s.add(Sum([If(day_city[d][Cities['Seville']], 1, 0) for d in range(15)]) == 3)

    # 4. Flight transitions: if a day is in two cities, they must be connected by a direct flight.
    for day in range(15):
        for c1 in range(4):
            for c2 in range(c1 + 1, 4):
                s.add(Implies(
                    And(day_city[day][c1], day_city[day][c2]),
                    Or(c2 in direct_flights[c1], c1 in direct_flights[c2])
                ))

    # 5. Additional constraints to ensure proper sequencing
    # After Madrid (days 0-6), must go to a connected city
    # We'll enforce that day 7 must include a city connected to Madrid
    s.add(Or(
        day_city[7][Cities['Paris']],
        day_city[7][Cities['Seville']],
        day_city[7][Cities['Bucharest']]
    ))
    s.add(Not(day_city[7][Cities['Madrid']]))

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(15):
            places = []
            for city in range(4):
                if is_true(m.evaluate(day_city[day][city])):
                    places.append(cities[city])
            itinerary.append({"day": day + 1, "place": places})
        
        # Verify all constraints are met
        days_in_cities = {city: 0 for city in cities}
        for day in itinerary:
            for place in day['place']:
                days_in_cities[place] += 1
        
        assert days_in_cities['Madrid'] == 7
        assert days_in_cities['Paris'] == 6
        assert days_in_cities['Bucharest'] == 2
        assert days_in_cities['Seville'] == 3
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))