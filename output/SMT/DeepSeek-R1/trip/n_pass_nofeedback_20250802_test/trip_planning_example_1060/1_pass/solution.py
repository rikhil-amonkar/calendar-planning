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
    
    start = {}
    for d in range(1, num_days + 1):
        for c in cities:
            start[(d, c)] = Bool(f"start_{d}_{c}")
    
    flight = {}
    for d in range(1, num_days + 1):
        for a, b in directed_flights:
            flight[(d, a, b)] = Bool(f"flight_{d}_{a}_{b}")
    
    in_city = {}
    for d in range(1, num_days + 1):
        for c in cities:
            base = start[(d, c)]
            flight_arrivals = []
            for a in cities:
                if (a, c) in directed_flights:
                    flight_arrivals.append(flight.get((d, a, c), False)
            if flight_arrivals:
                in_city[(d, c)] = Or(base, Or(flight_arrivals))
            else:
                in_city[(d, c)] = base
    
    for d in range(1, num_days + 1):
        flight_vars = []
        for (a, b) in directed_flights:
            flight_vars.append(flight[(d, a, b)])
        if flight_vars:
            solver.add(AtMostOne(flight_vars))
    
    for d in range(1, num_days + 1):
        for (a, b) in directed_flights:
            solver.add(Implies(flight[(d, a, b)], start[(d, a)]))
    
    start_day1 = [start[(1, c)] for c in cities]
    solver.add(AtLeastOne(*start_day1))
    solver.add(AtMostOne(*start_day1))
    
    for d in range(1, num_days):
        for c in cities:
            fly_from = []
            for b in cities:
                if (c, b) in directed_flights:
                    fly_from.append(flight[(d, c, b)])
            fly_from_city = Or(fly_from) if fly_from else False
            flight_arrivals = []
            for a in cities:
                if (a, c) in directed_flights:
                    flight_arrivals.append(flight[(d, a, c)])
            part1 = And(start[(d, c)], Not(fly_from_city))
            part2 = Or(flight_arrivals) if flight_arrivals else False
            if part2 == False:
                solver.add(start[(d + 1, c)] == part1)
            else:
                solver.add(start[(d + 1, c)] == Or(part1, part2))
    
    for d in [1, 2, 3, 4]:
        solver.add(in_city[(d, "Reykjavik")])
    solver.add(in_city[(4, "Stuttgart")])
    solver.add(in_city[(7, "Stuttgart")])
    for d in [13, 14, 15]:
        solver.add(in_city[(d, "Munich")])
    for d in [19, 20, 21, 22]:
        solver.add(in_city[(d, "Istanbul")])
    
    for c in cities:
        total_days = 0
        for d in range(1, num_days + 1):
            total_days += If(in_city[(d, c)], 1, 0)
        solver.add(total_days == durations[c])
    
    for d in range(1, num_days + 1):
        solver.add(Or([in_city[(d, c)] for c in cities]))
    
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for d in range(1, num_days + 1):
            flight_occurred = False
            arrival_city = None
            for (a, b) in directed_flights:
                if model.evaluate(flight.get((d, a, b), False)):
                    flight_occurred = True
                    arrival_city = b
                    break
            if flight_occurred:
                itinerary.append({"day": d, "place": arrival_city})
            else:
                for c in cities:
                    if model.evaluate(start[(d, c)]):
                        itinerary.append({"day": d, "place": c})
                        break
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()