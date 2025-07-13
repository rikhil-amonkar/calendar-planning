from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Dublin', 'Helsinki', 'Riga', 'Reykjavik', 'Vienna', 'Tallinn']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list
    direct_flights = {
        'Helsinki': ['Riga', 'Dublin', 'Tallinn', 'Reykjavik'],
        'Riga': ['Helsinki', 'Tallinn', 'Vienna', 'Dublin'],
        'Vienna': ['Riga', 'Reykjavik', 'Dublin'],
        'Reykjavik': ['Vienna', 'Helsinki', 'Dublin'],
        'Tallinn': ['Riga', 'Dublin', 'Helsinki'],
        'Dublin': ['Riga', 'Helsinki', 'Tallinn', 'Vienna', 'Reykjavik']
    }
    
    # Total days
    total_days = 15
    
    # Create a Z3 solver
    solver = Solver()
    
    # Variables: for each day (1..15), which city are we in?
    # day_city[d][c] is true if we are in city c on day d
    day_city = [[Bool(f"day_{d+1}_city_{c}") for c in cities] for d in range(total_days)]
    
    # Constraints
    
    # Each day, exactly one city is visited (accounting for flight days where two cities are involved)
    for d in range(total_days):
        # At least one city per day (could be two for flights)
        solver.add(Or([day_city[d][c] for c in range(len(cities))]))
    
    # Flight constraints: transitions between cities must be via direct flights
    for d in range(total_days - 1):
        current_day_cities = [day_city[d][c] for c in range(len(cities))]
        next_day_cities = [day_city[d+1][c] for c in range(len(cities))]
        
        # For each possible city pair (c1, c2), if we're in c1 on day d and c2 on day d+1, then there must be a flight.
        for c1 in range(len(cities)):
            for c2 in range(len(cities)):
                if c1 == c2:
                    continue  # staying in the same city, no flight
                city1 = cities[c1]
                city2 = cities[c2]
                if city2 not in direct_flights.get(city1, []):
                    # No direct flight, so this transition is impossible
                    solver.add(Not(And(day_city[d][c1], day_city[d+1][c2])))
    
    # Duration constraints
    # Dublin: 5 days
    dublin_days = Sum([If(day_city[d][city_map['Dublin']], 1, 0) for d in range(total_days)])
    solver.add(dublin_days == 5)
    
    # Helsinki: 3 days, with friends between day 3 and day 5 (inclusive)
    helsinki_days = Sum([If(day_city[d][city_map['Helsinki']], 1, 0) for d in range(total_days)])
    solver.add(helsinki_days == 3)
    # Friends between day 3 and 5: at least one of days 3,4,5 must be in Helsinki
    solver.add(Or([day_city[d][city_map['Helsinki']] for d in [2, 3, 4]))  # days are 1-based
    
    # Riga: 3 days
    riga_days = Sum([If(day_city[d][city_map['Riga']], 1, 0) for d in range(total_days)])
    solver.add(riga_days == 3)
    
    # Reykjavik: 2 days
    reykjavik_days = Sum([If(day_city[d][city_map['Reykjavik']], 1, 0) for d in range(total_days)])
    solver.add(reykjavik_days == 2)
    
    # Vienna: 2 days, show from day 2 to day 3 (so must be in Vienna on day 2 or 3)
    vienna_days = Sum([If(day_city[d][city_map['Vienna']], 1, 0) for d in range(total_days)])
    solver.add(vienna_days == 2)
    solver.add(Or(day_city[1][city_map['Vienna']], day_city[2][city_map['Vienna']]))  # days 2 and 3 (1-based)
    
    # Tallinn: 5 days, wedding between day 7 and 11 (so at least one day in 7-11 must be in Tallinn)
    tallinn_days = Sum([If(day_city[d][city_map['Tallinn']], 1, 0) for d in range(total_days)])
    solver.add(tallinn_days == 5)
    solver.add(Or([day_city[d][city_map['Tallinn']] for d in range(6, 11)]))  # days 7-11 (1-based)
    
    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        current_city = None
        start_day = 1
        for d in range(total_days):
            day = d + 1
            cities_in_day = [city for city in cities if model.evaluate(day_city[d][city_map[city]])]
            if len(cities_in_day) == 1:
                city = cities_in_day[0]
                if current_city != city:
                    if current_city is not None:
                        itinerary.append({"day_range": f"Day {start_day}-{day-1}", "place": current_city})
                    current_city = city
                    start_day = day
            else:
                if current_city is not None:
                    itinerary.append({"day_range": f"Day {start_day}-{day-1}", "place": current_city})
                for city in cities_in_day:
                    itinerary.append({"day_range": f"Day {day}", "place": city})
                current_city = None
                start_day = day + 1
        if current_city is not None:
            itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_city})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))