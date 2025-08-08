from z3 import *
import json

def main():
    cities = ["Reykjavik", "Stuttgart", "Istanbul", "Vilnius", "Seville", "Geneva", "Valencia", "Munich"]
    durations = {
        "Reykjavik": 4,
        "Stuttgart": 4,
        "Istanbul": 4,
        "Vilnius": 4,
        "Seville": 3,
        "Geneva": 5,
        "Valencia": 5,
        "Munich": 3
    }
    
    bidirectional = [
        ("Geneva", "Istanbul"),
        ("Reykjavik", "Munich"),
        ("Stuttgart", "Valencia"),
        ("Stuttgart", "Istanbul"),
        ("Munich", "Geneva"),
        ("Istanbul", "Vilnius"),
        ("Valencia", "Seville"),
        ("Valencia", "Istanbul"),
        ("Seville", "Munich"),
        ("Munich", "Istanbul"),
        ("Valencia", "Geneva"),
        ("Valencia", "Munich")
    ]
    unidirectional = [
        ("Reykjavik", "Stuttgart"),
        ("Vilnius", "Munich")
    ]
    
    directed_flights = set()
    for a, b in bidirectional:
        directed_flights.add((a, b))
        directed_flights.add((b, a))
    for a, b in unidirectional:
        directed_flights.add((a, b))
    
    solver = Solver()
    num_days = 25
    
    city_day = {}
    for d in range(1, num_days + 1):
        for c in cities:
            city_day[(d, c)] = Bool(f"day_{d}_{c}")
    
    for d in range(1, num_days + 1):
        solver.add(ExactlyOne([city_day[(d, c)] for c in cities]))
    
    for d in [1, 2, 3, 4]:
        solver.add(city_day[(d, "Reykjavik")])
    solver.add(city_day[(5, "Stuttgart")])
    solver.add(city_day[(7, "Stuttgart")])
    for d in [13, 14, 15]:
        solver.add(city_day[(d, "Munich")])
    for d in [19, 20, 21, 22]:
        solver.add(city_day[(d, "Istanbul")])
    
    for d in range(2, num_days + 1):
        for a in cities:
            for b in cities:
                if a == b:
                    continue
                if (a, b) not in directed_flights:
                    solver.add(Implies(
                        And(city_day[(d-1, a)], city_day[(d, b)]),
                        False
                    ))
    
    for c in cities:
        total_days = Sum([If(city_day[(d, c)], 1, 0) for d in range(1, num_days + 1)])
        solver.add(total_days == durations[c])
    
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        daily_places = [None] * num_days
        
        for d in range(1, num_days + 1):
            for c in cities:
                if model.eval(city_day[(d, c)]):
                    daily_places[d-1] = c
                    break
        
        current_city = daily_places[0]
        start_day = 1
        for day in range(1, num_days):
            if daily_places[day] != daily_places[day-1]:
                itinerary.append({
                    "day_range": f"Day {start_day}-{day}",
                    "place": daily_places[day-1]
                })
                start_day = day + 1
                current_city = daily_places[day]
        itinerary.append({
            "day_range": f"Day {start_day}-{num_days}",
            "place": daily_places[num_days-1]
        })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()