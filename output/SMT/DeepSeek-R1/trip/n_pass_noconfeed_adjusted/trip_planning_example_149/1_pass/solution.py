from z3 import *
import json

def main():
    # Define the cities
    City = Datatype('City')
    City.declare('London')
    City.declare('Santorini')
    City.declare('Istanbul')
    City = City.create()
    London, Santorini, Istanbul = City.London, City.Santorini, City.Istanbul
    
    # Days from 1 to 10
    n_days = 10
    days = list(range(1, n_days+1))
    
    # Variables for each day: the city we wake up in
    city_vars = [Const(f'city_{i}', City) for i in days]
    
    # Flight variables for days 1 to 9 (day 10 has no flight)
    flight_vars = [Bool(f'flight_{i}') for i in range(1, n_days)]
    
    solver = Solver()
    
    # Direct flight connections
    connected = [
        (Istanbul, London),
        (London, Istanbul),
        (London, Santorini),
        (Santorini, London)
    ]
    
    # Constraints for flights and city transitions
    for i in range(n_days - 1):
        # If we fly, the cities must be connected
        solver.add(Implies(flight_vars[i], Or([And(city_vars[i] == start, city_vars[i+1] == end) for start, end in connected])))
        # If we don't fly, stay in the same city
        solver.add(Implies(Not(flight_vars[i]), city_vars[i] == city_vars[i+1]))
    
    # No flight on the last day
    solver.add(Not(Bool(f'flight_{n_days}')))  # This variable doesn't exist, but for clarity
    
    # Conference constraints: must be in Santorini on day 5 and day 10
    # For day 5: either wake up in Santorini or fly to Santorini during day 5
    solver.add(Or(city_vars[4] == Santorini, And(flight_vars[4], city_vars[5] == Santorini)))
    # For day 10: wake up in Santorini (no flight)
    solver.add(city_vars[9] == Santorini)
    
    # Total days constraints
    total_london = 0
    total_santorini = 0
    total_istanbul = 0
    
    # For each day, determine if we are in each city
    for i in range(n_days):
        # For days 1-9, consider flight
        if i < n_days - 1:
            in_london = Or(city_vars[i] == London, And(flight_vars[i], city_vars[i+1] == London))
            in_santorini = Or(city_vars[i] == Santorini, And(flight_vars[i], city_vars[i+1] == Santorini))
            in_istanbul = Or(city_vars[i] == Istanbul, And(flight_vars[i], city_vars[i+1] == Istanbul))
        else:
            # Day 10: no flight
            in_london = (city_vars[i] == London)
            in_santorini = (city_vars[i] == Santorini)
            in_istanbul = (city_vars[i] == Istanbul)
        
        total_london += If(in_london, 1, 0)
        total_santorini += If(in_santorini, 1, 0)
        total_istanbul += If(in_istanbul, 1, 0)
    
    solver.add(total_london == 3)
    solver.add(total_santorini == 6)
    solver.add(total_istanbul == 3)
    
    # Check satisfiability
    if solver.check() == sat:
        model = solver.model()
        
        # Determine the presence in each city for each day
        presence = {city: [] for city in [London, Santorini, Istanbul]}
        for i in range(n_days):
            city_val = model.eval(city_vars[i])
            if i < n_days - 1:
                flight_val = model.eval(flight_vars[i])
            else:
                flight_val = False
                
            # Check presence in cities on day i+1 (0-indexed i corresponds to day i+1)
            if city_val == London:
                presence[London].append(i+1)
            if city_val == Santorini:
                presence[Santorini].append(i+1)
            if city_val == Istanbul:
                presence[Istanbul].append(i+1)
                
            if flight_val:
                next_city_val = model.eval(city_vars[i+1])
                if next_city_val == London:
                    presence[London].append(i+1)
                if next_city_val == Santorini:
                    presence[Santorini].append(i+1)
                if next_city_val == Istanbul:
                    presence[Istanbul].append(i+1)
        
        # Remove duplicates and sort the days for each city
        for city in presence:
            presence[city] = sorted(set(presence[city]))
        
        # Group consecutive days for each city
        itinerary = []
        for city, days_list in presence.items():
            if not days_list:
                continue
            groups = []
            start = days_list[0]
            prev = days_list[0]
            for day in days_list[1:]:
                if day == prev + 1:
                    prev = day
                else:
                    groups.append((start, prev))
                    start = day
                    prev = day
            groups.append((start, prev))
            
            for start, end in groups:
                if start == end:
                    day_range = f"Day {start}"
                else:
                    day_range = f"Day {start}-{end}"
                itinerary.append({
                    "day_range": day_range,
                    "place": str(city)
                })
        
        # Sort itinerary by the start day
        itinerary.sort(key=lambda x: int(x['day_range'].split(' ')[1].split('-')[0]))
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()