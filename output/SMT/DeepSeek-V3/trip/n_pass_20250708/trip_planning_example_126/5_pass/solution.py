from z3 import *

def solve_itinerary():
    s = Solver()

    # Days and cities
    days = list(range(1, 12))  # Days 1-11
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

    # Total days in each city (counting flight days for both cities)
    krakow_days = []
    paris_days = []
    seville_days = []
    
    for i in range(len(days)):
        # Current day counts for current city
        krakow_days.append(If(assignments[i] == city_map['Krakow'], 1, 0))
        paris_days.append(If(assignments[i] == city_map['Paris'], 1, 0))
        seville_days.append(If(assignments[i] == city_map['Seville'], 1, 0))
        
        # If this is a flight day (different from next day), count for both cities
        if i < len(days)-1:
            krakow_days[-1] = If(And(assignments[i] == city_map['Krakow'], 
                                   assignments[i+1] != city_map['Krakow']),
                               1, krakow_days[-1])
            paris_days[-1] = If(And(assignments[i] == city_map['Paris'],
                                  assignments[i+1] != city_map['Paris']),
                              1, paris_days[-1])
            seville_days[-1] = If(And(assignments[i] == city_map['Seville'],
                                    assignments[i+1] != city_map['Seville']),
                                1, seville_days[-1])

    s.add(Sum(krakow_days) == 5)
    s.add(Sum(paris_days) == 2)
    s.add(Sum(seville_days) == 6)

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

        # Verify solution meets all constraints
        day_counts = {city: 0 for city in cities}
        for entry in itinerary:
            if '-' in entry['day_range']:
                start, end = map(int, entry['day_range'].replace('Day ', '').split('-'))
                day_counts[entry['place']] += end - start + 1
            else:
                day_counts[entry['place']] += 1

        assert sum(day_counts.values()) == 11, "Total days must be 11"
        assert day_counts['Krakow'] == 5, "Must spend exactly 5 days in Krakow"
        assert day_counts['Paris'] == 2, "Must spend exactly 2 days in Paris"
        assert day_counts['Seville'] == 6, "Must spend exactly 6 days in Seville"

        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    print(result)
else:
    print("No valid itinerary found.")