from z3 import *

def solve_itinerary():
    s = Solver()

    # Days and cities
    days = range(1, 12)  # Days 1-11
    cities = ['Krakow', 'Paris', 'Seville']
    city_map = {city: idx for idx, city in enumerate(cities)}

    # Decision variables - city for each day
    assignments = [Int(f'day_{day}') for day in days]

    # Each day must be assigned a valid city
    for day in days:
        s.add(Or([assignments[day-1] == city_map[city] for city in cities]))

    # Flight constraints - only direct flights allowed
    for i in range(len(days)-1):
        current = assignments[i]
        next_day = assignments[i+1]
        s.add(Or(
            current == next_day,  # Stay in same city
            And(current == city_map['Krakow'], next_day == city_map['Paris']),
            And(current == city_map['Paris'], next_day == city_map['Krakow']),
            And(current == city_map['Paris'], next_day == city_map['Seville']),
            And(current == city_map['Seville'], next_day == city_map['Paris'])
        ))

    # Total days in each city
    s.add(Sum([If(assignments[i] == city_map['Krakow'], 1, 0) for i in range(len(days))]) == 5)
    s.add(Sum([If(assignments[i] == city_map['Paris'], 1, 0) for i in range(len(days))]) == 2)
    s.add(Sum([If(assignments[i] == city_map['Seville'], 1, 0) for i in range(len(days))]) == 6)

    # Workshop in Krakow between days 1-5
    s.add(Or([assignments[i] == city_map['Krakow'] for i in range(5)]))

    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_city = None
        start_day = 1

        for day in days:
            city_idx = model[assignments[day-1]].as_long()
            city = cities[city_idx]

            if current_city is None:
                current_city = city
                start_day = day
            elif city != current_city:
                # Add previous city's stay
                if start_day == day-1:
                    itinerary.append({'day_range': f'Day {start_day}', 'place': current_city})
                else:
                    itinerary.append({'day_range': f'Day {start_day}-{day-1}', 'place': current_city})
                # Add flight day records
                itinerary.append({'day_range': f'Day {day}', 'place': current_city})
                itinerary.append({'day_range': f'Day {day}', 'place': city})
                current_city = city
                start_day = day

        # Add last city's stay
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