from z3 import *
import json

def solve_itinerary():
    # Cities and their required stay days
    cities = {
        "Santorini": 3,
        "Valencia": 4,
        "Madrid": 2,
        "Seville": 2,
        "Bucharest": 3,
        "Vienna": 4,
        "Riga": 4,
        "Tallinn": 5,
        "Krakow": 5,
        "Frankfurt": 4
    }
    
    # Direct flights
    direct_flights = {
        "Vienna": ["Bucharest", "Seville", "Valencia", "Madrid", "Krakow", "Frankfurt", "Riga", "Santorini"],
        "Bucharest": ["Vienna", "Riga", "Valencia", "Santorini", "Frankfurt", "Madrid"],
        "Santorini": ["Madrid", "Bucharest", "Vienna"],
        "Madrid": ["Santorini", "Valencia", "Seville", "Bucharest", "Frankfurt", "Vienna"],
        "Seville": ["Valencia", "Vienna", "Madrid"],
        "Valencia": ["Seville", "Madrid", "Bucharest", "Vienna", "Krakow", "Frankfurt"],
        "Krakow": ["Valencia", "Frankfurt", "Vienna"],
        "Frankfurt": ["Valencia", "Krakow", "Vienna", "Tallinn", "Bucharest", "Riga", "Madrid"],
        "Riga": ["Bucharest", "Vienna", "Frankfurt", "Tallinn"],
        "Tallinn": ["Riga", "Frankfurt"]
    }
    
    # Total days
    total_days = 27
    days = list(range(1, total_days + 1))
    
    # Create a Z3 solver
    solver = Solver()
    
    # Variables: for each day, which city are we in?
    day_city = {}
    for d in days:
        day_city[d] = {}
        for c in cities:
            day_city[d][c] = Bool(f"day_{d}_city_{c}")
    
    # Constraints:
    # 1. Each day, you are in exactly one city (except travel days where you are in two)
    for d in days:
        # At least one city per day
        solver.add(Or([day_city[d][c] for c in cities]))
        # At most two cities per day (for travel days)
        for c1 in cities:
            for c2 in cities:
                if c1 != c2:
                    solver.add(Implies(And(day_city[d][c1], day_city[d][c2]), 
                                  (c1, c2) in [(x, y) for x in direct_flights for y in direct_flights[x]]))
    
    # 2. Stay durations
    for c in cities:
        total_days_in_city = Sum([If(day_city[d][c], 1, 0) for d in days])
        solver.add(total_days_in_city == cities[c])
    
    # 3. Fixed events
    # Wedding in Vienna between day 3 and day 6
    for d in range(3, 7):
        solver.add(day_city[d]["Vienna"])
    
    # Show in Madrid from day 6 to day 7
    solver.add(day_city[6]["Madrid"])
    solver.add(day_city[7]["Madrid"])
    
    # Conference in Riga from day 20 to day 23
    for d in range(20, 24):
        solver.add(day_city[d]["Riga"])
    
    # Workshop in Tallinn from day 23 to day 27
    for d in range(23, 28):
        solver.add(day_city[d]["Tallinn"])
    
    # Friends in Krakow from day 11 to day 15
    for d in range(11, 16):
        solver.add(day_city[d]["Krakow"])
    
    # 4. Flight connections
    for d in range(1, total_days):
        for c1 in cities:
            for c2 in cities:
                if c1 != c2:
                    solver.add(Implies(And(day_city[d][c1], day_city[d + 1][c2]), 
                                  (c1, c2) in [(x, y) for x in direct_flights for y in direct_flights[x]]))
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        current_city = None
        start_day = 1
        for d in days:
            for c in cities:
                if is_true(model[day_city[d][c]]):
                    if current_city != c:
                        if current_city is not None:
                            itinerary.append({"day_range": f"Day {start_day}-{d - 1}", "place": current_city})
                            itinerary.append({"day_range": f"Day {d - 1}", "place": current_city})
                            itinerary.append({"day_range": f"Day {d - 1}", "place": c})
                        current_city = c
                        start_day = d
        itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_city})
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible itinerary found"}

# Execute the solver
result = solve_itinerary()
print(json.dumps(result, indent=2))