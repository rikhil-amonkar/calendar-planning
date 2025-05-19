import json

def calculate_itinerary():
    # Input parameters
    total_days = 17
    cities = {
        'Riga': 7,
        'Budapest': 7,
        'Paris': 4,
        'Warsaw': 2
    }
    wedding_in_riga = (11, 17)
    warsaw_show = (1, 2)
    direct_flights = {
        'Warsaw': ['Budapest', 'Riga', 'Paris'],
        'Budapest': ['Warsaw', 'Paris'],
        'Paris': ['Budapest', 'Warsaw', 'Riga'],
        'Riga': ['Warsaw', 'Paris']
    }

    # Initialize itinerary
    itinerary = []

    # Day 1-2: Warsaw for the show
    current_day = 1
    end_day = warsaw_show[1]
    itinerary.append({
        'day_range': f'Day {current_day}-{end_day}',
        'place': 'Warsaw'
    })
    current_day = end_day + 1

    # Next destination after Warsaw (must be a city with direct flight from Warsaw)
    remaining_cities = {k: v for k, v in cities.items() if k != 'Warsaw'}
    possible_next = [city for city in direct_flights['Warsaw'] if city in remaining_cities]

    # We need to ensure Riga is visited during wedding days (11-17)
    # So Riga must be last city (since wedding is towards the end)
    # So after Warsaw, we can go to Budapest or Paris

    # Try Budapest next
    next_city = 'Budapest'
    if next_city in possible_next:
        # Fly to Budapest
        itinerary.append({
            'flying': f'Day {current_day}-{current_day}',
            'from': 'Warsaw',
            'to': 'Budapest'
        })
        current_day += 1

        # Stay in Budapest for 7 days
        stay_days = cities['Budapest']
        end_day = current_day + stay_days - 1
        itinerary.append({
            'day_range': f'Day {current_day}-{end_day}',
            'place': 'Budapest'
        })
        current_day = end_day + 1

        # Next from Budapest (can go to Paris)
        next_city = 'Paris'
        if next_city in direct_flights['Budapest']:
            # Fly to Paris
            itinerary.append({
                'flying': f'Day {current_day}-{current_day}',
                'from': 'Budapest',
                'to': 'Paris'
            })
            current_day += 1

            # Stay in Paris for 4 days
            stay_days = cities['Paris']
            end_day = current_day + stay_days - 1
            itinerary.append({
                'day_range': f'Day {current_day}-{end_day}',
                'place': 'Paris'
            })
            current_day = end_day + 1

            # Finally fly to Riga for wedding
            if 'Riga' in direct_flights['Paris']:
                # Fly to Riga
                itinerary.append({
                    'flying': f'Day {current_day}-{current_day}',
                    'from': 'Paris',
                    'to': 'Riga'
                })
                current_day += 1

                # Stay in Riga for 7 days (must cover days 11-17)
                stay_days = cities['Riga']
                end_day = current_day + stay_days - 1
                itinerary.append({
                    'day_range': f'Day {current_day}-{end_day}',
                    'place': 'Riga'
                })

    # Verify the itinerary covers all constraints
    # Check if Riga covers wedding days (11-17)
    riga_visit = None
    for item in itinerary:
        if item.get('place') == 'Riga':
            riga_visit = item['day_range']
            break

    if riga_visit:
        start, end = map(int, riga_visit.split('Day ')[1].split('-'))
        if not (start <= wedding_in_riga[0] and end >= wedding_in_riga[1]):
            # If not, try alternative path: Warsaw -> Paris -> Budapest -> Riga
            itinerary = []

            # Day 1-2: Warsaw
            current_day = 1
            end_day = warsaw_show[1]
            itinerary.append({
                'day_range': f'Day {current_day}-{end_day}',
                'place': 'Warsaw'
            })
            current_day = end_day + 1

            # Fly to Paris
            itinerary.append({
                'flying': f'Day {current_day}-{current_day}',
                'from': 'Warsaw',
                'to': 'Paris'
            })
            current_day += 1

            # Stay in Paris for 4 days
            stay_days = cities['Paris']
            end_day = current_day + stay_days - 1
            itinerary.append({
                'day_range': f'Day {current_day}-{end_day}',
                'place': 'Paris'
            })
            current_day = end_day + 1

            # Fly to Budapest
            itinerary.append({
                'flying': f'Day {current_day}-{current_day}',
                'from': 'Paris',
                'to': 'Budapest'
            })
            current_day += 1

            # Stay in Budapest for 7 days
            stay_days = cities['Budapest']
            end_day = current_day + stay_days - 1
            itinerary.append({
                'day_range': f'Day {current_day}-{end_day}',
                'place': 'Budapest'
            })
            current_day = end_day + 1

            # Fly to Riga
            itinerary.append({
                'flying': f'Day {current_day}-{current_day}',
                'from': 'Budapest',
                'to': 'Riga'
            })
            current_day += 1

            # Stay in Riga for 7 days
            stay_days = cities['Riga']
            end_day = current_day + stay_days - 1
            itinerary.append({
                'day_range': f'Day {current_day}-{end_day}',
                'place': 'Riga'
            })

    return itinerary

itinerary = calculate_itinerary()
print(json.dumps(itinerary, indent=2))