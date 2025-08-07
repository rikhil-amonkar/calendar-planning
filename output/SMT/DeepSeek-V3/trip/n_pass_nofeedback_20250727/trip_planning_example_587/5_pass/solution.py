from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Manchester', 'Istanbul', 'Venice', 'Krakow', 'Lyon']
    city_map = {city: idx for idx, city in enumerate(cities)}
    manchester = city_map['Manchester']
    istanbul = city_map['Istanbul']
    venice = city_map['Venice']
    krakow = city_map['Krakow']
    lyon = city_map['Lyon']
    
    # Direct flights: adjacency list
    direct_flights = {
        manchester: [venice, istanbul, krakow],
        istanbul: [manchester, venice, krakow, lyon],
        venice: [manchester, istanbul, lyon],
        krakow: [manchester, istanbul],
        lyon: [venice, istanbul]
    }
    
    # Days: 1..21
    days = 21
    day_range = range(1, days + 1)
    
    # Create a solver instance
    s = Solver()
    
    # Variables: for each day, which cities are we in?
    # presence[d][c] is True if we are in city c on day d
    presence = [[Bool(f"presence_day{day}_city{city}") for city in range(len(cities))] for day in day_range]
    
    # Variables: flight transitions. flight_from_to[d][from_city][to_city] is True if we fly from from_city to to_city on day d.
    flight_from_to = [[[Bool(f"flight_day{day}_from{from_city}_to{to_city}") 
                        for to_city in range(len(cities))] 
                        for from_city in range(len(cities))] 
                        for day in day_range]
    
    # Constraints
    
    # 1. On each day, we are in at least one city. (But can be in two cities if it's a flight day)
    for day in day_range:
        s.add(Or([presence[day-1][city] for city in range(len(cities))]))
    
    # 2. Flight transitions: if flight_from_to[d][from][to], then:
    #    - presence[d][from] and presence[d][to] must be true.
    #    - from and to must have a direct flight.
    for day in day_range:
        for from_city in range(len(cities)):
            for to_city in range(len(cities)):
                if to_city == from_city:
                    continue
                # If flight from from_city to to_city on day, then:
                implies_flight = Implies(
                    flight_from_to[day-1][from_city][to_city],
                    And(
                        presence[day-1][from_city],
                        presence[day-1][to_city],
                        to_city in direct_flights[from_city]
                    )
                )
                s.add(implies_flight)
    
    # 3. Flight uniqueness: on any day, at most one flight can occur (or none).
    for day in day_range:
        flight_possibilities = []
        for from_city in range(len(cities)):
            for to_city in range(len(cities)):
                if from_city != to_city and to_city in direct_flights[from_city]:
                    flight_possibilities.append(flight_from_to[day-1][from_city][to_city])
        s.add(AtMost(*flight_possibilities, 1))
    
    # 4. Continuity between days: 
    #    If we are in city c on day d, then either:
    #    - we were in c on day d-1, or
    #    - there's a flight to c on day d (from any city), or
    #    - it's day 1.
    for day in day_range:
        for city in range(len(cities)):
            if day == 1:
                continue  # no previous day
            prev_day_in_city = presence[day-2][city]
            flight_to_city = Or([flight_from_to[day-2][from_city][city] for from_city in range(len(cities)) if city != from_city and city in direct_flights.get(from_city, [])])
            s.add(Implies(presence[day-1][city], Or(prev_day_in_city, flight_to_city)))
    
    # 5. Total days per city constraints.
    total_days = [0]*len(cities)
    for city in range(len(cities)):
        total_days[city] = Sum([If(presence[day-1][city], 1, 0) for day in day_range])
    
    s.add(total_days[manchester] == 3)
    s.add(total_days[istanbul] == 7)
    s.add(total_days[venice] == 7)
    s.add(total_days[krakow] == 6)
    s.add(total_days[lyon] == 2)
    
    # 6. Manchester must include days 1-3.
    for day in [1, 2, 3]:
        s.add(presence[day-1][manchester])
    
    # 7. Venice must include days 3-9.
    for day in range(3, 10):
        s.add(presence[day-1][venice])
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in day_range:
            current_day = {'day': day, 'cities': []}
            for city in range(len(cities)):
                if is_true(m.evaluate(presence[day-1][city])):
                    current_day['cities'].append(cities[city])
            itinerary.append(current_day)
        
        # Construct the JSON output
        json_output = {'itinerary': []}
        for entry in itinerary:
            day_num = entry['day']
            cities_present = entry['cities']
            for city in cities_present:
                json_output['itinerary'].append({'day': day_num, 'place': city})
        
        return json_output
    else:
        return {"error": "No valid itinerary found"}

# Generate the solution
solution = solve_itinerary()
print(json.dumps(solution, indent=2))