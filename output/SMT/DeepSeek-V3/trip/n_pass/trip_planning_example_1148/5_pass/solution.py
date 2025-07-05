from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = ["Lisbon", "Dubrovnik", "Copenhagen", "Prague", "Tallinn", "Stockholm", "Split", "Lyon"]
    req_days = {
        "Lisbon": 2,
        "Dubrovnik": 5,
        "Copenhagen": 5,
        "Prague": 3,
        "Tallinn": 2,
        "Stockholm": 4,
        "Split": 3,
        "Lyon": 2
    }
    
    # Direct flight connections
    flights = {
        "Dubrovnik": ["Stockholm", "Copenhagen"],
        "Lisbon": ["Copenhagen", "Lyon", "Stockholm", "Prague"],
        "Copenhagen": ["Lisbon", "Stockholm", "Split", "Dubrovnik", "Prague", "Tallinn"],
        "Prague": ["Stockholm", "Lyon", "Lisbon", "Split", "Copenhagen", "Tallinn"],
        "Tallinn": ["Stockholm", "Copenhagen", "Prague"],
        "Stockholm": ["Dubrovnik", "Copenhagen", "Prague", "Tallinn", "Lisbon", "Split"],
        "Split": ["Copenhagen", "Stockholm", "Prague", "Lyon"],
        "Lyon": ["Lisbon", "Prague", "Split"]
    }
    
    # Create solver
    s = Solver()
    
    # Variables: day_city[day][city] = True if in city on that day
    days = 19
    day_city = [[Bool(f"d{day}c{city}") for city in cities] for day in range(days)]
    
    # Flight variables: flight_day[day] = True if day has a flight
    flight_day = [Bool(f"f{day}") for day in range(days-1)]
    
    # Constraints
    
    # 1. Each non-flight day is in exactly one city
    # Each flight day is in exactly two cities
    for day in range(days):
        if day < days-1:
            s.add(Implies(flight_day[day], 
                         Sum([If(day_city[day][i], 1, 0) for i in range(len(cities))]) == 2))
            s.add(Implies(Not(flight_day[day]), 
                         Sum([If(day_city[day][i], 1, 0) for i in range(len(cities))]) == 1))
        else:
            s.add(Sum([If(day_city[day][i], 1, 0) for i in range(len(cities))]) == 1)
    
    # 2. Total days per city must match requirements
    for city_idx, city in enumerate(cities):
        total = Sum([If(day_city[day][city_idx], 1, 0) for day in range(days)])
        s.add(total == req_days[city])
    
    # 3. Event constraints
    # Tallinn meeting day 1 or 2
    s.add(Or(day_city[0][cities.index("Tallinn")], day_city[1][cities.index("Tallinn")]))
    # Lisbon workshop day 4 or 5
    s.add(Or(day_city[3][cities.index("Lisbon")], day_city[4][cities.index("Lisbon")]))
    # Stockholm wedding day 13-16
    s.add(Or([day_city[12+i][cities.index("Stockholm")] for i in range(4)]))
    # Lyon show day 18 or 19
    s.add(Or(day_city[17][cities.index("Lyon")], day_city[18][cities.index("Lyon")]))
    
    # 4. Flight connections
    for day in range(days-1):
        for c1 in range(len(cities)):
            for c2 in range(len(cities)):
                if c1 == c2:
                    continue
                # If transitioning from c1 to c2, must have direct flight
                if cities[c2] not in flights[cities[c1]]:
                    s.add(Implies(And(day_city[day][c1], day_city[day+1][c2]), flight_day[day]))
                    s.add(Implies(And(day_city[day][c1], day_city[day+1][c2]), 
                                 day_city[day][c2]))  # Flight day includes both cities
    
    # Solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        current_place = None
        start_day = 1
        
        for day in range(days):
            day_num = day + 1
            active_cities = [city for city_idx, city in enumerate(cities) 
                           if m.evaluate(day_city[day][city_idx])]
            
            if len(active_cities) == 1:
                city = active_cities[0]
                if current_place is None:
                    current_place = (start_day, day_num, city)
                else:
                    if current_place[2] == city:
                        current_place = (current_place[0], day_num, city)
                    else:
                        itinerary.append({
                            "day_range": f"Day {current_place[0]}-{current_place[1]}", 
                            "place": current_place[2]
                        })
                        current_place = (day_num, day_num, city)
            else:
                if current_place is not None:
                    itinerary.append({
                        "day_range": f"Day {current_place[0]}-{current_place[1]}", 
                        "place": current_place[2]
                    })
                    current_place = None
                for city in active_cities:
                    itinerary.append({
                        "day_range": f"Day {day_num}",
                        "place": city
                    })
        
        if current_place is not None:
            itinerary.append({
                "day_range": f"Day {current_place[0]}-{current_place[1]}", 
                "place": current_place[2]
            })
        
        # Verify total days
        total = 0
        for entry in itinerary:
            if '-' in entry["day_range"]:
                s, e = map(int, entry["day_range"].split('Day ')[1].split('-'))
                total += (e - s + 1)
            else:
                total += 1
        
        if total != 19:
            return {"error": "Invalid day count in itinerary"}
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Run the solver
itinerary = solve_itinerary()
print(itinerary)