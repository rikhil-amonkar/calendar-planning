import z3
import json
import sys

def main():
    try:
        # Represent cities as integers
        cities = {
            'Vienna': 0,
            'Milan': 1,
            'Rome': 2,
            'Riga': 3,
            'Lisbon': 4,
            'Vilnius': 5,
            'Oslo': 6
        }
        inv_cities = {v: k for k, v in cities.items()}
        
        # Define flight connections (bidirectional and unidirectional)
        connections = [
            # Bidirectional flights
            (cities['Riga'], cities['Oslo']),
            (cities['Rome'], cities['Oslo']),
            (cities['Vienna'], cities['Milan']),
            (cities['Vienna'], cities['Vilnius']),
            (cities['Vienna'], cities['Lisbon']),
            (cities['Riga'], cities['Milan']),
            (cities['Lisbon'], cities['Oslo']),
            (cities['Rome'], cities['Lisbon']),
            (cities['Vienna'], cities['Riga']),
            (cities['Vienna'], cities['Rome']),
            (cities['Milan'], cities['Oslo']),
            (cities['Vienna'], cities['Oslo']),
            (cities['Vilnius'], cities['Oslo']),
            (cities['Vilnius'], cities['Milan']),
            (cities['Riga'], cities['Lisbon']),
            (cities['Milan'], cities['Lisbon']),
            # Unidirectional flights
            (cities['Rome'], cities['Riga']),
            (cities['Riga'], cities['Vilnius'])
        ]
        allowed_flights = set()
        for a, b in connections:
            allowed_flights.add((a, b))
            allowed_flights.add((b, a))

        # Create Z3 variables
        city_vars = [z3.Int(f'c_{i}') for i in range(15)]  # City each day
        fly_vars = [z3.Bool(f'f_{i}') for i in range(14)]   # Flight each day
        
        solver = z3.Solver()
        
        # City must be between 0-6
        for c in city_vars:
            solver.add(z3.And(c >= 0, c <= 6))
            
        # Start in Vienna on day 1
        solver.add(city_vars[0] == cities['Vienna'])
        
        # Flight constraints
        for i in range(14):
            # If no flight, same city next day
            solver.add(z3.Implies(z3.Not(fly_vars[i]), city_vars[i] == city_vars[i+1]))
            # If flight, different city and valid connection
            solver.add(z3.Implies(fly_vars[i], city_vars[i] != city_vars[i+1]))
            solver.add(z3.Implies(fly_vars[i], z3.Or(
                [z3.And(city_vars[i] == a, city_vars[i+1] == b) for (a, b) in allowed_flights]
            )))
        
        # Total flights must be exactly 6
        solver.add(z3.Sum([z3.If(fly, 1, 0) for fly in fly_vars]) == 6)
        
        # Calculate days per city (including flight days)
        day_counts = [0] * 7
        for city_idx in range(7):
            # Days starting in city
            start_days = z3.Sum([z3.If(city_vars[i] == city_idx, 1, 0) for i in range(15)])
            # Flight arrivals to city
            flight_arrivals = z3.Sum([z3.If(z3.And(fly_vars[i], city_vars[i+1] == city_idx), 1, 0) for i in range(14)])
            day_counts[city_idx] = start_days + flight_arrivals
        
        # Duration constraints
        solver.add(day_counts[cities['Vienna']] == 4)
        solver.add(day_counts[cities['Milan']] == 2)
        solver.add(day_counts[cities['Rome']] == 3)
        solver.add(day_counts[cities['Riga']] == 2)
        solver.add(day_counts[cities['Lisbon']] == 3)
        solver.add(day_counts[cities['Vilnius']] == 4)
        solver.add(day_counts[cities['Oslo']] == 3)
        
        # Day 4 must be in Vienna
        solver.add(z3.Or(
            city_vars[3] == cities['Vienna'],  # Starts day 4 in Vienna
            z3.And(fly_vars[3], city_vars[4] == cities['Vienna'])  # Arrives on day 4
        ))
        
        # Lisbon between days 11-13
        lisbon_days = []
        for day in [10, 11, 12]:  # Days 11,12,13 (0-indexed days 10,11,12)
            lisbon_days.append(city_vars[day] == cities['Lisbon'])
            if day < 14:
                lisbon_days.append(z3.And(fly_vars[day], city_vars[day+1] == cities['Lisbon']))
        solver.add(z3.Or(lisbon_days))
        
        # Oslo between days 13-15
        oslo_days = []
        for day in [12, 13, 14]:  # Days 13,14,15 (0-indexed days 12,13,14)
            oslo_days.append(city_vars[day] == cities['Oslo'])
            if day < 14:
                oslo_days.append(z3.And(fly_vars[day], city_vars[day+1] == cities['Oslo']))
        solver.add(z3.Or(oslo_days))
        
        # Solve and output
        if solver.check() == z3.sat:
            m = solver.model()
            itinerary = []
            for day in range(15):
                city_val = m.eval(city_vars[day]).as_long()
                places = [inv_cities[city_val]]
                # Check if flight day
                if day < 14 and m.eval(fly_vars[day]):
                    next_city_val = m.eval(city_vars[day+1]).as_long()
                    if next_city_val != city_val:
                        places.append(inv_cities[next_city_val])
                itinerary.append({"day": day+1, "place": places})
            print(json.dumps({"itinerary": itinerary}))
        else:
            print('{"itinerary": []}')
            
    except Exception as e:
        print(f'{{"error": "Solver failed: {str(e)}"}}', file=sys.stderr)
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()