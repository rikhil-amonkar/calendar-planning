from z3 import *

def solve_itinerary():
    s = Solver()

    # Define the problem parameters
    cities = ['Dublin', 'Riga', 'Vilnius']
    city_idx = {city: i for i, city in enumerate(cities)}
    required_days = {'Dublin': 2, 'Riga': 5, 'Vilnius': 7}
    flights = {
        'Dublin': ['Riga'],
        'Riga': ['Dublin', 'Vilnius'],
        'Vilnius': ['Riga']
    }

    # Create day variables (1-12)
    day_vars = [Int(f'day_{i}') for i in range(1, 13)]
    for var in day_vars:
        s.add(Or([var == city_idx[city] for city in cities]))

    # Constraint: Total days in each city
    for city in cities:
        s.add(Sum([If(var == city_idx[city], 1, 0) for var in day_vars]) == required_days[city])

    # Constraint: Valid transitions between cities
    for i in range(11):
        current = day_vars[i]
        next_day = day_vars[i+1]
        s.add(Or(
            current == next_day,  # Stay in same city
            # Or take a direct flight
            Or([And(current == city_idx[depart], next_day == city_idx[arrive])
                for depart in flights for arrive in flights[depart]])
        ))

    # Solve and format the output
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_city = None
        start_day = 1

        for day in range(1, 13):
            city = cities[model.evaluate(day_vars[day-1]).as_long()]
            if current_city is None:
                current_city = city
                start_day = day
            elif city != current_city:
                # Add stay for previous city
                if start_day == day-1:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day-1}", "place": current_city})
                # Add flight day records
                itinerary.append({"day_range": f"Day {day}", "place": current_city})
                itinerary.append({"day_range": f"Day {day}", "place": city})
                current_city = city
                start_day = day

        # Add final stay
        if start_day == 12:
            itinerary.append({"day_range": f"Day 12", "place": current_city})
        else:
            itinerary.append({"day_range": f"Day {start_day}-12", "place": current_city})

        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

itinerary = solve_itinerary()
print(itinerary)