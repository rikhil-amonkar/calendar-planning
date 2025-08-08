from z3 import *
import json

def main():
    cities_dict = {
        "Bucharest": 0,
        "Venice": 1,
        "Prague": 2,
        "Frankfurt": 3,
        "Zurich": 4,
        "Florence": 5,
        "Tallinn": 6
    }
    city_names = {v: k for k, v in cities_dict.items()}
    
    # Define direct flight connections (both directions)
    edges = [
        (2, 6), (6, 2),  # Prague <-> Tallinn
        (2, 4), (4, 2),  # Prague <-> Zurich
        (5, 2), (2, 5),  # Florence <-> Prague
        (3, 0), (0, 3),  # Frankfurt <-> Bucharest
        (3, 1), (1, 3),  # Frankfurt <-> Venice
        (2, 0), (0, 2),  # Prague <-> Bucharest
        (0, 4), (4, 0),  # Bucharest <-> Zurich
        (6, 3), (3, 6),  # Tallinn <-> Frankfurt
        (4, 5), (5, 4),  # Zurich <-> Florence (added missing return flight)
        (3, 4), (4, 3),  # Frankfurt <-> Zurich
        (4, 1), (1, 4),  # Zurich <-> Venice
        (5, 3), (3, 5),  # Florence <-> Frankfurt
        (2, 3), (3, 2),  # Prague <-> Frankfurt
        (6, 4), (4, 6)   # Tallinn <-> Zurich
    ]
    
    # Required days per city
    required_days = [3, 5, 4, 5, 5, 5, 5]  # [Bucharest, Venice, Prague, Frankfurt, Zurich, Florence, Tallinn]
    
    # Create Z3 variables for each day (0 = start of day1, 1-26 = end of each day)
    cities = [Int(f'city_{i}') for i in range(27)]
    s = Solver()
    
    # Each city variable must be between 0-6
    for c in cities:
        s.add(c >= 0, c <= 6)
    
    # Flight constraints: consecutive days must be same city or have direct flight
    for i in range(1, 27):
        current_edges = []
        for a, b in edges:
            current_edges.append(And(cities[i-1] == a, cities[i] == b))
        s.add(Or(cities[i-1] == cities[i], Or(current_edges)))
    
    # Constraint: total days per city must match requirements
    for c in range(7):
        total = 0
        for i in range(1, 27):
            # Count day if either start or end is in city c
            total += If(Or(cities[i-1] == c, cities[i] == c), 1, 0)
        s.add(total == required_days[c])
    
    # Event constraints: must be in specific cities during certain periods
    # Venice between days 22-26
    venice_days = []
    for day in range(22, 27):  # Days 22 to 26 inclusive
        # Check if either start or end of day is in Venice
        venice_days.append(Or(cities[day-1] == cities_dict["Venice"], cities[day] == cities_dict["Venice"]))
    s.add(Or(venice_days))
    
    # Frankfurt between days 12-16
    frankfurt_days = []
    for day in range(12, 17):  # Days 12 to 16 inclusive
        frankfurt_days.append(Or(cities[day-1] == cities_dict["Frankfurt"], cities[day] == cities_dict["Frankfurt"]))
    s.add(Or(frankfurt_days))
    
    # Tallinn between days 8-12
    tallinn_days = []
    for day in range(8, 13):  # Days 8 to 12 inclusive
        tallinn_days.append(Or(cities[day-1] == cities_dict["Tallinn"], cities[day] == cities_dict["Tallinn"]))
    s.add(Or(tallinn_days))
    
    # Solve and output itinerary
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_city = model[cities[0]].as_long()
        start_day = 1
        # Group consecutive days in the same city
        for day in range(1, 27):
            city_val = model[cities[day]].as_long()
            if city_val != current_city:
                itinerary.append({
                    'day_range': f'Day {start_day}-{day}',
                    'place': city_names[current_city]
                })
                current_city = city_val
                start_day = day + 1
        # Add last city
        itinerary.append({
            'day_range': f'Day {start_day}-26',
            'place': city_names[current_city]
        })
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()