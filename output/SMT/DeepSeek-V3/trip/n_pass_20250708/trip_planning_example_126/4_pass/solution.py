from z3 import *

def solve_itinerary():
    s = Solver()

    # Days and cities
    days = list(range(1, 12))  # Days 1-11
    cities = ['Krakow', 'Paris', 'Seville']
    city_map = {'Krakow': 0, 'Paris': 1, 'Seville': 2}

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

        # Verify total days match requirements
        day_counts = {city: 0 for city in cities}
        for entry in itinerary:
            if '-' in entry['day_range']:
                start, end = map(int, entry['day_range'].replace('Day ', '').split('-'))
                day_counts[entry['place']] += end - start + 1
            else:
                day_counts[entry['place']] += 1

        assert sum(day_counts.values()) == 11
        assert day_counts['Krakow'] == 5
        assert day_counts['Paris'] == 2
        assert day_counts['Seville'] == 6

        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    print(result)
else:
    print("No valid itinerary found.")