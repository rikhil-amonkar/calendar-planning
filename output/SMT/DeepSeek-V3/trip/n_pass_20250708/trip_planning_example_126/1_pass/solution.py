from z3 import *

def solve_itinerary():
    # Create the solver
    s = Solver()

    # Define the days and cities
    days = range(1, 12)  # Days 1 to 11
    cities = ['Krakow', 'Paris', 'Seville']

    # Variables to represent the city on each day
    city_vars = [Int(f'day_{day}') for day in days]
    # Assign each city a unique integer
    city_map = {'Krakow': 0, 'Paris': 1, 'Seville': 2}

    # Constraints for each day: must be one of the cities
    for day_var in city_vars:
        s.add(Or([day_var == city_map[city] for city in cities]))

    # Flight constraints: direct flights are Krakow-Paris and Paris-Seville
    for i in range(len(days) - 1):
        day1 = city_vars[i]
        day2 = city_vars[i + 1]
        s.add(Or(
            day1 == day2,  # Stay in the same city
            And(day1 == city_map['Krakow'], day2 == city_map['Paris']),  # Krakow -> Paris
            And(day1 == city_map['Paris'], day2 == city_map['Krakow']),  # Paris -> Krakow
            And(day1 == city_map['Paris'], day2 == city_map['Seville']),  # Paris -> Seville
            And(day1 == city_map['Seville'], day2 == city_map['Paris'])   # Seville -> Paris
        ))

    # Total days in each city
    total_krakow = Sum([If(city_vars[i] == city_map['Krakow'], 1, 0) for i in range(len(days))])
    total_paris = Sum([If(city_vars[i] == city_map['Paris'], 1, 0) for i in range(len(days))])
    total_seville = Sum([If(city_vars[i] == city_map['Seville'], 1, 0) for i in range(len(days))])

    s.add(total_krakow == 5)
    s.add(total_paris == 2)
    s.add(total_seville == 6)

    # Workshop in Krakow between day 1 and day 5
    s.add(Or([city_vars[i] == city_map['Krakow'] for i in range(0, 5)]))

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_city = None
        start_day = 1

        # Generate the itinerary
        for day in days:
            day_var = city_vars[day - 1]
            city_idx = model[day_var].as_long()
            city = cities[city_idx]

            if current_city is None:
                current_city = city
                start_day = day
            elif city != current_city:
                # Add the previous city's stay
                if start_day == day - 1:
                    itinerary.append({'day_range': f'Day {start_day}', 'place': current_city})
                else:
                    itinerary.append({'day_range': f'Day {start_day}-{day - 1}', 'place': current_city})
                # Add the flight day for the previous city
                itinerary.append({'day_range': f'Day {day}', 'place': current_city})
                # Add the flight day for the new city
                itinerary.append({'day_range': f'Day {day}', 'place': city})
                current_city = city
                start_day = day

        # Add the last city's stay
        if start_day == days[-1]:
            itinerary.append({'day_range': f'Day {start_day}', 'place': current_city})
        else:
            itinerary.append({'day_range': f'Day {start_day}-{days[-1]}', 'place': current_city})

        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    print(result)
else:
    print("No valid itinerary found.")