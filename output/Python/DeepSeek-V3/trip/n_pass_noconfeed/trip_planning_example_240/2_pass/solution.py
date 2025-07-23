import json

def calculate_itinerary():
    # Define constraints
    total_days = 12
    cities = {
        'Prague': {'days': 2},
        'Berlin': {'days': 3, 'conference_days': [6, 8]},
        'Tallinn': {'days': 5, 'relative_days': (8, 12)},
        'Stockholm': {'days': 5}
    }
    
    # Direct flights
    direct_flights = {
        'Berlin': ['Tallinn', 'Stockholm'],
        'Tallinn': ['Berlin', 'Prague', 'Stockholm'],
        'Prague': ['Tallinn', 'Stockholm'],
        'Stockholm': ['Prague', 'Berlin', 'Tallinn']
    }
    
    # Initialize itinerary
    itinerary = []
    current_city = None
    remaining_days = total_days
    day = 1
    
    # Helper function to find next city
    def get_next_city(current, visited):
        possible = []
        for city in cities:
            if city != current and city not in visited:
                if current is None or city in direct_flights.get(current, []):
                    possible.append(city)
        return possible
    
    # Assign Berlin conference days first
    berlin_conf_days = cities['Berlin']['conference_days']
    for conf_day in berlin_conf_days:
        if day <= conf_day:
            # Fill days before conference
            if day < conf_day:
                # Need to be in Berlin by conf_day
                # Find a city that can reach Berlin
                if current_city is None:
                    # Start in Berlin or a city connected to Berlin
                    possible_start = ['Berlin'] + direct_flights['Berlin']
                    for start_city in possible_start:
                        if start_city in cities and cities[start_city]['days'] > 0:
                            current_city = start_city
                            break
                else:
                    # Transition to Berlin
                    if 'Berlin' in direct_flights[current_city]:
                        # Add transition day
                        itinerary.append({'day_range': f'Day {day}-{day}', 'place': current_city})
                        day += 1
                        current_city = 'Berlin'
                    else:
                        # Find intermediate city
                        intermediate = list(set(direct_flights[current_city]) & set(direct_flights['Berlin']))
                        if intermediate:
                            itinerary.append({'day_range': f'Day {day}-{day}', 'place': current_city})
                            day += 1
                            current_city = intermediate[0]
                            itinerary.append({'day_range': f'Day {day}-{day}', 'place': current_city})
                            day += 1
                            current_city = 'Berlin'
            # Add Berlin conference day
            itinerary.append({'day_range': f'Day {day}-{day}', 'place': 'Berlin'})
            cities['Berlin']['days'] -= 1
            day += 1
    
    # Assign Tallinn relative days
    tallinn_start, tallinn_end = cities['Tallinn']['relative_days']
    if day <= tallinn_start:
        # Need to be in Tallinn by tallinn_start
        if current_city is None:
            current_city = 'Tallinn'
        else:
            if 'Tallinn' in direct_flights[current_city]:
                # Transition to Tallinn
                itinerary.append({'day_range': f'Day {day}-{day}', 'place': current_city})
                day += 1
                current_city = 'Tallinn'
            else:
                # Find intermediate city
                intermediate = list(set(direct_flights[current_city]) & set(direct_flights['Tallinn']))
                if intermediate:
                    itinerary.append({'day_range': f'Day {day}-{day}', 'place': current_city})
                    day += 1
                    current_city = intermediate[0]
                    itinerary.append({'day_range': f'Day {day}-{day}', 'place': current_city})
                    day += 1
                    current_city = 'Tallinn'
        # Stay in Tallinn until day 12
        stay_days = tallinn_end - day + 1
        itinerary.append({'day_range': f'Day {day}-{day + stay_days - 1}', 'place': 'Tallinn'})
        cities['Tallinn']['days'] -= stay_days
        day += stay_days
    
    # Assign remaining days to other cities
    remaining_cities = [city for city in cities if cities[city]['days'] > 0]
    for city in remaining_cities:
        if cities[city]['days'] > 0:
            if current_city is None:
                current_city = city
            else:
                if city in direct_flights[current_city]:
                    # Transition to city
                    itinerary.append({'day_range': f'Day {day}-{day}', 'place': current_city})
                    day += 1
                    current_city = city
                else:
                    # Find intermediate city
                    intermediate = list(set(direct_flights[current_city]) & set(direct_flights[city]))
                    if intermediate:
                        itinerary.append({'day_range': f'Day {day}-{day}', 'place': current_city})
                        day += 1
                        current_city = intermediate[0]
                        itinerary.append({'day_range': f'Day {day}-{day}', 'place': current_city})
                        day += 1
                        current_city = city
            # Stay in city for remaining days
            stay_days = cities[city]['days']
            itinerary.append({'day_range': f'Day {day}-{day + stay_days - 1}', 'place': city})
            day += stay_days
    
    # Post-process itinerary to merge consecutive days in same city
    merged_itinerary = []
    i = 0
    while i < len(itinerary):
        current = itinerary[i]
        j = i + 1
        while j < len(itinerary) and itinerary[j]['place'] == current['place']:
            j += 1
        
        # Parse day ranges safely
        def parse_day(day_str):
            return int(day_str.replace('Day', '').strip())
        
        if j > i + 1:
            # Merge
            try:
                start_day = parse_day(current['day_range'].split('-')[0])
                end_day = parse_day(itinerary[j-1]['day_range'].split('-')[1])
                merged_itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': current['place']})
            except:
                # If parsing fails, just keep the original entries
                merged_itinerary.extend(itinerary[i:j])
            i = j
        else:
            merged_itinerary.append(current)
            i += 1
    
    return {'itinerary': merged_itinerary}

# Execute and print result
result = calculate_itinerary()
print(json.dumps(result, indent=2))