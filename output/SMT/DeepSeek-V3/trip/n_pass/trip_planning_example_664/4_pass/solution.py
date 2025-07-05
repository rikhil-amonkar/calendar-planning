from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Tallinn": 2,
        "Bucharest": 4,
        "Seville": 5,
        "Stockholm": 5,
        "Munich": 5,
        "Milan": 2
    }
    
    # Direct flights as a dictionary for easy lookup
    direct_flights = {
        "Milan": ["Stockholm", "Munich", "Seville"],
        "Stockholm": ["Milan", "Munich", "Tallinn"],
        "Munich": ["Stockholm", "Bucharest", "Seville", "Milan", "Tallinn"],
        "Bucharest": ["Munich"],
        "Seville": ["Munich", "Milan"],
        "Tallinn": ["Stockholm", "Munich"]
    }
    
    # Days are 1..18
    days = 18
    
    # Create a solver instance
    s = Solver()
    
    # Variables: for each day, which city are we in?
    # day_city[d][c] is true if we are in city c on day d
    day_city = [[Bool(f"day_{day}_city_{city}") for city in cities] for day in range(1, days+1)]
    
    # Flight variables: flight_from_to[d][i][j] is true if we fly from city i to city j on day d
    flight_from_to = [[[Bool(f"flight_{day}_{city1}_{city2}") 
                       for city2 in cities] 
                      for city1 in cities] 
                     for day in range(1, days)]
    
    # Constraints
    
    # 1. Each day, exactly one city is active (or two if it's a flight day)
    for day in range(1, days + 1):
        s.add(AtLeast(*[day_city[day-1][list(cities.keys()).index(city)] for city in cities], 1))
        s.add(AtMost(*[day_city[day-1][list(cities.keys()).index(city)] for city in cities], 2))
    
    # 2. Flight constraints: if you fly from city i to city j on day d, then:
    # - on day d, you are in i and j
    # - on day d-1, you were in i
    # - on day d+1, you are in j
    # Also, flights must be direct.
    for day in range(1, days):
        for i, city1 in enumerate(cities):
            for j, city2 in enumerate(cities):
                if i == j:
                    s.add(Not(flight_from_to[day-1][i][j]))  # no self-flights
                else:
                    if city2 not in direct_flights.get(city1, []):
                        s.add(Not(flight_from_to[day-1][i][j]))  # no indirect flights
                    else:
                        # If flight from i to j on day, then:
                        # day is in i and j, day-1 is in i, day+1 is in j
                        s.add(Implies(flight_from_to[day-1][i][j], 
                                     And(day_city[day-1][i], day_city[day][j])))
                        if day > 1:
                            s.add(Implies(flight_from_to[day-1][i][j], day_city[day-2][i]))
    
    # 3. No consecutive flights: you can't have flight on day d and d+1
    for day in range(1, days - 1):
        s.add(Not(Or([And(flight_from_to[day-1][i][j], flight_from_to[day][k][l]) 
                      for i in range(len(cities)) 
                      for j in range(len(cities)) 
                      for k in range(len(cities)) 
                      for l in range(len(cities))])))
    
    # 4. Duration constraints
    # Tallinn: 2 days
    s.add(Sum([If(day_city[day][list(cities.keys()).index("Tallinn")], 1, 0) for day in range(days)]) == 2)
    # Bucharest: 4 days, between day 1 and 4
    s.add(Sum([If(day_city[day][list(cities.keys()).index("Bucharest")], 1, 0) for day in range(4)]) == 4)
    # Seville: 5 days, between day 8 and 12
    s.add(Sum([If(day_city[day][list(cities.keys()).index("Seville")], 1, 0) for day in range(7, 12)]) == 5)
    # Stockholm: 5 days
    s.add(Sum([If(day_city[day][list(cities.keys()).index("Stockholm")], 1, 0) for day in range(days)]) == 5)
    # Munich: 5 days, between day 4 and 8
    s.add(Sum([If(day_city[day][list(cities.keys()).index("Munich")], 1, 0) for day in range(3, 8)]) == 5)
    # Milan: 2 days
    s.add(Sum([If(day_city[day][list(cities.keys()).index("Milan")], 1, 0) for day in range(days)]) == 2)
    
    # 5. Initial and final constraints
    # The first day must be in Bucharest (since you visit relatives there between day 1-4)
    s.add(day_city[0][list(cities.keys()).index("Bucharest")])
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        
        # Extract the itinerary
        itinerary = []
        day_to_places = {}
        for day in range(1, days + 1):
            places = []
            for city in cities:
                if model.evaluate(day_city[day-1][list(cities.keys()).index(city)]):
                    places.append(city)
            day_to_places[day] = places
        
        # Build the itinerary with day ranges
        current_place = None
        start_day = 1
        for day in range(1, days + 1):
            places = day_to_places[day]
            if len(places) == 1:
                place = places[0]
                if current_place is None:
                    current_place = place
                    start_day = day
                elif place == current_place:
                    continue
                else:
                    if start_day == day - 1:
                        itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                    else:
                        itinerary.append({"day_range": f"Day {start_day}-{day-1}", "place": current_place})
                    current_place = place
                    start_day = day
            else:
                if current_place is not None:
                    if start_day == day - 1:
                        itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                    else:
                        itinerary.append({"day_range": f"Day {start_day}-{day-1}", "place": current_place})
                for place in places:
                    itinerary.append({"day_range": f"Day {day}", "place": place})
                current_place = None
                start_day = day + 1
        
        if current_place is not None:
            if start_day == days:
                itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{days}", "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Execute the function and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))