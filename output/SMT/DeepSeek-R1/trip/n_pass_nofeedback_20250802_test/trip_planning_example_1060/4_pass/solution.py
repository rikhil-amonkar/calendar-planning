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
                    flight_arrivals.append(flight[(d, a, c)])
            if flight_arrivals:
                in_city[(d, c)] = Or(base, Or(flight_arrivals))
            else:
                in_city[(d, c)] = base
    
    for d in range(1, num_days + 1):
        flight_vars = [flight[(d, a, b)] for (a, b) in directed_flights]
        if flight_vars:
            solver.add(AtMost(*flight_vars, 1))
    
    for d in range(1, num_days + 1):
        for (a, b) in directed_flights:
            solver.add(Implies(flight[(d, a, b)], start[(d, a)]))
    
    start_day1 = [start[(1, c)] for c in cities]
    solver.add(Or(start_day1))
    solver.add(AtMost(*start_day1, 1))
    
    for d in range(1, num_days):
        for c in cities:
            fly_from = [flight[(d, c, b)] for b in cities if (c, b) in directed_flights]
            fly_from_city = Or(fly_from) if fly_from else False
            flight_arrivals = [flight[(d, a, c)] for a in cities if (a, c) in directed_flights]
            part1 = And(start[(d, c)], Not(fly_from_city)) if fly_from_city is not False else start[(d, c)]
            part2 = Or(flight_arrivals) if flight_arrivals else False
            
            if part2 is False:
                solver.add(start[(d+1, c)] == part1)
            else:
                solver.add(start[(d+1, c)] == Or(part1, part2))
    
    # Fixed constraints
    for d in [1, 2, 3, 4]:
        solver.add(in_city[(d, "Reykjavik")])
    solver.add(in_city[(4, "Stuttgart")])
    solver.add(in_city[(7, "Stuttgart")])
    for d in [13, 14, 15]:
        solver.add(in_city[(d, "Munich")])
    for d in [19, 20, 21, 22]:
        solver.add(in_city[(d, "Istanbul")])
    
    # Duration constraints
    for c in cities:
        total_days = Sum([If(in_city[(d, c)], 1, 0) for d in range(1, num_days + 1)])
        solver.add(total_days == durations[c])
    
    # Each day must be in at least one city
    for d in range(1, num_days + 1):
        solver.add(Or([in_city[(d, c)] for c in cities]))
    
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        current_place = None
        start_day = 1
        current_start_day = 1
        
        # Build day-by-day itinerary
        daily_places = []
        for d in range(1, num_days + 1):
            flight_occurred = False
            arrival_city = None
            for (a, b) in directed_flights:
                if is_true(model.eval(flight[(d, a, b)])):
                    flight_occurred = True
                    arrival_city = b
                    break
            if flight_occurred:
                daily_places.append(arrival_city)
            else:
                for c in cities:
                    if is_true(model.eval(start[(d, c)])):
                        daily_places.append(c)
                        break
        
        # Group consecutive days
        current_place = daily_places[0]
        start_day = 1
        for day in range(1, num_days):
            if daily_places[day] != daily_places[day-1]:
                itinerary.append({
                    "day_range": f"Day {start_day}-{day}",
                    "place": daily_places[day-1]
                })
                start_day = day + 1
                current_place = daily_places[day]
        itinerary.append({
            "day_range": f"Day {start_day}-{num_days}",
            "place": daily_places[num_days-1]
        })
        
        # Validate durations
        city_days = {city: 0 for city in cities}
        for day in range(num_days):
            city_days[daily_places[day]] += 1
        
        valid = True
        for city, req in durations.items():
            if city_days[city] != req:
                print(f"Validation failed: {city} has {city_days[city]} days (expected {req})")
                valid = False
        
        if valid:
            result = {"itinerary": itinerary}
            print(json.dumps(result, indent=2))
        else:
            print("Invalid solution generated")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()