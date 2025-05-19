import json

def calculate_itinerary():
    # Input parameters
    total_days = 13
    cities = {
        'Seville': 2,
        'Stuttgart': 7,
        'Porto': 3,
        'Madrid': 4
    }
    conference_days = [7, 13]
    relatives_madrid_range = (1, 4)
    direct_flights = {
        'Porto': ['Stuttgart', 'Seville', 'Madrid'],
        'Seville': ['Porto', 'Madrid'],
        'Madrid': ['Porto', 'Seville'],
        'Stuttgart': ['Porto']
    }

    # Initialize itinerary
    itinerary = []
    current_day = 1

    # Must be in Madrid between day 1 and 4
    madrid_days = min(cities['Madrid'], relatives_madrid_range[1] - relatives_madrid_range[0] + 1)
    itinerary.append({
        'day_range': f'Day {current_day}-{current_day + madrid_days - 1}',
        'place': 'Madrid'
    })
    current_day += madrid_days
    remaining_madrid_days = cities['Madrid'] - madrid_days

    # Must be in Stuttgart on day 7
    # Check if we can fit Seville or Porto before day 7
    days_until_conference = 7 - current_day
    if days_until_conference > 0:
        # Try to fit Seville first (2 days)
        if 'Seville' in direct_flights['Madrid'] and cities['Seville'] > 0 and days_until_conference >= cities['Seville']:
            itinerary.append({
                'flying': f'Day {current_day}-{current_day}',
                'from': 'Madrid',
                'to': 'Seville'
            })
            current_day += 1
            itinerary.append({
                'day_range': f'Day {current_day}-{current_day + cities["Seville"] - 1}',
                'place': 'Seville'
            })
            current_day += cities["Seville"]
            cities["Seville"] = 0

        # Or try to fit Porto (3 days)
        elif 'Porto' in direct_flights['Madrid'] and cities['Porto'] > 0 and days_until_conference >= cities['Porto']:
            itinerary.append({
                'flying': f'Day {current_day}-{current_day}',
                'from': 'Madrid',
                'to': 'Porto'
            })
            current_day += 1
            itinerary.append({
                'day_range': f'Day {current_day}-{current_day + cities["Porto"] - 1}',
                'place': 'Porto'
            })
            current_day += cities["Porto"]
            cities["Porto"] = 0

    # Must be in Stuttgart on day 7
    if current_day <= 7:
        itinerary.append({
            'flying': f'Day {current_day}-{current_day}',
            'from': itinerary[-1]['place'],
            'to': 'Stuttgart'
        })
        current_day += 1
        stay_days = 7 - current_day + 1
        itinerary.append({
            'day_range': f'Day {current_day}-{current_day + stay_days - 1}',
            'place': 'Stuttgart'
        })
        current_day += stay_days
        cities['Stuttgart'] -= stay_days

    # Now handle remaining cities after day 7
    remaining_cities = {city: days for city, days in cities.items() if days > 0}
    for city, days in remaining_cities.items():
        if city == 'Stuttgart':
            continue  # Will handle Stuttgart last

        # Check if we can fly to this city from current location
        current_location = itinerary[-1]['place']
        if city in direct_flights.get(current_location, []):
            itinerary.append({
                'flying': f'Day {current_day}-{current_day}',
                'from': current_location,
                'to': city
            })
            current_day += 1
            itinerary.append({
                'day_range': f'Day {current_day}-{current_day + days - 1}',
                'place': city
            })
            current_day += days
        else:
            # Need to find an intermediate city
            intermediate_cities = set(direct_flights[current_location]) & set(direct_flights[city])
            if intermediate_cities:
                intermediate = intermediate_cities.pop()
                itinerary.append({
                    'flying': f'Day {current_day}-{current_day}',
                    'from': current_location,
                    'to': intermediate
                })
                current_day += 1
                itinerary.append({
                    'flying': f'Day {current_day}-{current_day}',
                    'from': intermediate,
                    'to': city
                })
                current_day += 1
                itinerary.append({
                    'day_range': f'Day {current_day}-{current_day + days - 1}',
                    'place': city
                })
                current_day += days

    # Must be in Stuttgart on day 13
    if current_day <= 13:
        stay_days = 13 - current_day + 1
        current_location = itinerary[-1]['place']
        if current_location != 'Stuttgart':
            itinerary.append({
                'flying': f'Day {current_day}-{current_day}',
                'from': current_location,
                'to': 'Stuttgart'
            })
            current_day += 1
            stay_days -= 1
        itinerary.append({
            'day_range': f'Day {current_day}-{current_day + stay_days - 1}',
            'place': 'Stuttgart'
        })

    return itinerary

if __name__ == "__main__":
    itinerary = calculate_itinerary()
    print(json.dumps(itinerary, indent=2))