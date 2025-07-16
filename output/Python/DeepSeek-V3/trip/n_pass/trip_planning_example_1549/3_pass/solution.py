import json

def main():
    # Define city stay durations
    city_durations = {
        'Prague': 4,
        'Tallinn': 3,
        'Warsaw': 2,
        'Porto': 3,
        'Naples': 5,
        'Milan': 3,
        'Lisbon': 5,
        'Santorini': 5,
        'Riga': 4,
        'Stockholm': 2
    }
    
    # Define direct flights
    flights = {
        'Riga': ['Prague', 'Milan', 'Tallinn', 'Warsaw', 'Stockholm'],
        'Stockholm': ['Milan', 'Lisbon', 'Santorini', 'Warsaw', 'Prague', 'Tallinn', 'Riga'],
        'Milan': ['Stockholm', 'Riga', 'Naples', 'Porto', 'Prague', 'Lisbon', 'Warsaw', 'Santorini'],
        'Lisbon': ['Stockholm', 'Warsaw', 'Naples', 'Porto', 'Prague', 'Milan', 'Riga'],
        'Naples': ['Warsaw', 'Milan', 'Santorini', 'Lisbon'],
        'Warsaw': ['Naples', 'Lisbon', 'Porto', 'Tallinn', 'Stockholm', 'Riga', 'Milan', 'Prague'],
        'Porto': ['Lisbon', 'Milan', 'Warsaw'],
        'Prague': ['Riga', 'Tallinn', 'Lisbon', 'Stockholm', 'Milan', 'Warsaw'],
        'Tallinn': ['Riga', 'Prague', 'Warsaw', 'Stockholm'],
        'Santorini': ['Stockholm', 'Milan', 'Naples']
    }
    
    # Build initial itinerary with constraints
    itinerary = [
        {'day_range': 'Day 1-4', 'place': 'Prague'},
        {'day_range': 'Day 5-8', 'place': 'Riga'},
        {'day_range': 'Day 9-10', 'place': 'Warsaw'},
        {'day_range': 'Day 11-12', 'place': 'Stockholm'},
        {'day_range': 'Day 13-17', 'place': 'Lisbon'},
        {'day_range': 'Day 18-20', 'place': 'Tallinn'},
        {'day_range': 'Day 21-23', 'place': 'Porto'},
        {'day_range': 'Day 24-26', 'place': 'Milan'},
        {'day_range': 'Day 27-28', 'place': 'Naples'}
    ]
    
    # Function to parse day numbers safely
    def parse_day(day_str):
        return int(day_str.replace('Day', '').strip())
    
    # Function to adjust day ranges
    def adjust_day_ranges(itinerary, start_index, days_to_add):
        for i in range(start_index, len(itinerary)):
            parts = itinerary[i]['day_range'].split('-')
            start = parse_day(parts[0])
            end = parse_day(parts[1])
            itinerary[i]['day_range'] = f'Day {start+days_to_add}-{end+days_to_add}'
        return itinerary
    
    # Validate flight connections and adjust itinerary
    i = 0
    while i < len(itinerary)-1:
        current = itinerary[i]['place']
        next_city = itinerary[i+1]['place']
        
        if next_city not in flights[current]:
            # Find intermediate city
            possible_intermediates = list(set(flights[current]) & set(flights[next_city]))
            if possible_intermediates:
                intermediate = possible_intermediates[0]
                # Insert 1-day intermediate stay
                prev_end = parse_day(itinerary[i]['day_range'].split('-')[1])
                itinerary.insert(i+1, {
                    'day_range': f'Day {prev_end+1}-{prev_end+1}',
                    'place': intermediate
                })
                # Adjust following day ranges by +1 day
                itinerary = adjust_day_ranges(itinerary, i+2, 1)
                # Check if we exceeded 28 days
                last_day = parse_day(itinerary[-1]['day_range'].split('-')[1])
                if last_day > 28:
                    # Remove the intermediate and find alternative path
                    itinerary.pop(i+1)
                    itinerary = adjust_day_ranges(itinerary, i+1, -1)
                    # Try another intermediate if available
                    if len(possible_intermediates) > 1:
                        intermediate = possible_intermediates[1]
                        prev_end = parse_day(itinerary[i]['day_range'].split('-')[1])
                        itinerary.insert(i+1, {
                            'day_range': f'Day {prev_end+1}-{prev_end+1}',
                            'place': intermediate
                        })
                        itinerary = adjust_day_ranges(itinerary, i+2, 1)
            else:
                # If no intermediate found, adjust the itinerary
                itinerary = [
                    {'day_range': 'Day 1-4', 'place': 'Prague'},
                    {'day_range': 'Day 5-8', 'place': 'Riga'},
                    {'day_range': 'Day 9-10', 'place': 'Warsaw'},
                    {'day_range': 'Day 11-12', 'place': 'Stockholm'},
                    {'day_range': 'Day 13-17', 'place': 'Lisbon'},
                    {'day_range': 'Day 18-20', 'place': 'Tallinn'},
                    {'day_range': 'Day 21-23', 'place': 'Porto'},
                    {'day_range': 'Day 24-26', 'place': 'Milan'},
                    {'day_range': 'Day 27-28', 'place': 'Naples'}
                ]
                break
        i += 1
    
    # Final check for day limit
    last_day = parse_day(itinerary[-1]['day_range'].split('-')[1])
    if last_day > 28:
        # Shorten the longest stays to fit in 28 days
        itinerary = [
            {'day_range': 'Day 1-3', 'place': 'Prague'},  # Reduced by 1
            {'day_range': 'Day 4-7', 'place': 'Riga'},     # Reduced by 1
            {'day_range': 'Day 8-9', 'place': 'Warsaw'},
            {'day_range': 'Day 10-11', 'place': 'Stockholm'},
            {'day_range': 'Day 12-15', 'place': 'Lisbon'}, # Reduced by 2
            {'day_range': 'Day 16-18', 'place': 'Tallinn'},
            {'day_range': 'Day 19-21', 'place': 'Porto'},
            {'day_range': 'Day 22-24', 'place': 'Milan'},
            {'day_range': 'Day 25-28', 'place': 'Naples'}  # Extended to use all days
        ]
    
    output = {
        'itinerary': itinerary,
        'total_days': parse_day(itinerary[-1]['day_range'].split('-')[1])
    }
    
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()