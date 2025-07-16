import json
from collections import deque

def main():
    # Define city stay durations (minimum days)
    city_durations = {
        'Prague': 3,
        'Tallinn': 2,
        'Warsaw': 2,
        'Porto': 2,
        'Naples': 3,
        'Milan': 2,
        'Lisbon': 3,
        'Santorini': 3,
        'Riga': 3,
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
    
    # Function to find shortest path between two cities
    def find_connection(start, end):
        if end in flights[start]:
            return []
        
        visited = {start}
        queue = deque()
        queue.append((start, []))
        
        while queue:
            city, path = queue.popleft()
            for neighbor in flights[city]:
                if neighbor == end:
                    return path + [neighbor]
                if neighbor not in visited:
                    visited.add(neighbor)
                    queue.append((neighbor, path + [neighbor]))
        return None
    
    # Create initial itinerary with minimum durations
    cities_to_visit = ['Prague', 'Riga', 'Warsaw', 'Stockholm', 'Lisbon', 'Tallinn', 'Porto', 'Milan', 'Naples']
    itinerary = []
    current_day = 1
    
    for i in range(len(cities_to_visit)-1):
        current_city = cities_to_visit[i]
        next_city = cities_to_visit[i+1]
        
        # Add current city to itinerary
        duration = city_durations[current_city]
        itinerary.append({
            'day_range': f'Day {current_day}-{current_day + duration - 1}',
            'place': current_city
        })
        current_day += duration
        
        # Check if direct flight exists
        if next_city not in flights[current_city]:
            # Find connecting path
            connection = find_connection(current_city, next_city)
            if connection:
                # Add 1-day stopovers for connecting cities
                for stopover in connection[:-1]:
                    itinerary.append({
                        'day_range': f'Day {current_day}-{current_day}',
                        'place': stopover
                    })
                    current_day += 1
    
    # Add the last city
    last_city = cities_to_visit[-1]
    duration = city_durations[last_city]
    itinerary.append({
        'day_range': f'Day {current_day}-{current_day + duration - 1}',
        'place': last_city
    })
    current_day += duration - 1
    
    # Now extend the itinerary to 28 days by adding days to existing stays
    remaining_days = 28 - current_day
    
    # Distribute extra days to cities that can have extended stays
    extendable_cities = [city for city in city_durations if city in [item['place'] for item in itinerary]]
    
    # Add extra days to cities in order, one day at a time until we reach 28 days
    while remaining_days > 0:
        for i in range(len(itinerary)):
            if remaining_days <= 0:
                break
            current_item = itinerary[i]
            city = current_item['place']
            # Only extend stays that aren't stopovers (1-day stays)
            start, end = map(parse_day, current_item['day_range'].split('-'))
            if end - start + 1 >= city_durations[city]:
                # Extend this stay by 1 day
                new_end = end + 1
                current_item['day_range'] = f'Day {start}-{new_end}'
                remaining_days -= 1
                # Adjust subsequent day ranges
                for j in range(i+1, len(itinerary)):
                    next_start, next_end = map(parse_day, itinerary[j]['day_range'].split('-'))
                    itinerary[j]['day_range'] = f'Day {next_start+1}-{next_end+1}'
    
    # Final itinerary
    output = {
        'itinerary': itinerary,
        'total_days': parse_day(itinerary[-1]['day_range'].split('-')[1])
    }
    
    print(json.dumps(output, indent=2))

def parse_day(day_str):
    return int(day_str.replace('Day', '').strip())

if __name__ == '__main__':
    main()